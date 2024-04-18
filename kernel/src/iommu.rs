//! IOMMU.
//!
//! ## Glossary
//!
//! - PASID: Process Address Space Identifier that identifies the address space targeted by DMA requests.

use core::mem::MaybeUninit;
use core::ops::Range;
use core::pin::Pin;
use core::ptr;

use bit_field::BitField;

use astd::sync::Mutex;

static IOMMU: Mutex<Option<RemappingHardware>> = Mutex::new(None);
static mut NAIVE_MAP: NaiveIommuMap = NaiveIommuMap::new();

const MAXPHYADDR: u64 = 56;
const PAGE_SZ: u64 = 4096;
const PAGE_MASK: u64 = !(PAGE_SZ - 1);
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

pub struct RemappingHardware {
    base: u64,
    cap: u64,
    ecap: u64,
}

pub struct NaiveIommuMap {
    root_table: RootTable,
    context_table: ContextTable,
}

#[repr(transparent)]
struct RootTable {
    entries: [MaybeUninit<RootTableEntry>; 256],
}

#[repr(transparent)]
struct ContextTable {
    entries: [MaybeUninit<ContextTableEntry>; 256],
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct RootTableEntry {
    lower: u64,
    upper: u64,
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct ContextTableEntry {
    lower: u64,
    upper: u64,
}

impl RemappingHardware {
    const VER_REG: usize = 0;
    const CAP_REG: usize = 0x08;
    const ECAP_REG: usize = 0x10;
    const GCMD_REG: usize = 0x18;
    const GSTS_REG: usize = 0x1c;
    const RTADDR_REG: usize = 0x20;
    const CCMD_REG: usize = 0x28;

    const IOTLB_REG_OFFSET: usize = 0x8;

    const CAP_ESRTPS: usize = 63;               // ESRTPS: Enhanced Set Root Table Pointer Support

    const GCMD_TE: usize = 31;                  // TE: Translation Enable
    const GCMD_SRTP: usize = 30;                // SRTP: Set Root Table Pointer

    const CCMD_ICC: usize = 63;                 // ICC: Invalidate Context-Cache
    const CCMD_CIRG: Range<usize> = 61..63;     // CIRG: Context Invalidation Request Granularity
    const CCMD_CIRG_GLOBAL: u64 = 0b01;

    const IOTLBCMD_IVT: usize = 63;             // IVT: Invalidate IOTLB
    const IOTLBCMD_DID: Range<usize> = 32..48;  // DID: Domain-ID
    const IOTLBCMD_IIRG: Range<usize> = 60..62; // IIRG: IOTLB Invalidation Request Granularity
    const IOTLBCMD_IIRG_GLOBAL: u64 = 0b01;
    const IOTLBCMD_IIRG_DOMAIN: u64 = 0b10;
    const IOTLBCMD_IIRG_PAGE: u64 = 0b11;

    pub unsafe fn new(base: u64) -> Self {
        let mut s = Self {
            base,
            cap: 0,
            ecap: 0,
        };

        s.cap = s.read_u64(Self::CAP_REG);
        s.ecap = s.read_u64(Self::ECAP_REG);

        s
    }

    pub fn version(&self) -> u32 {
        unsafe {
            self.read_u32(Self::VER_REG)
        }
    }

    pub fn root_table_addr(&self) -> u64 {
        unsafe {
            self.read_u64(Self::RTADDR_REG)
        }
    }

    pub fn global_status(&self) -> u32 {
        unsafe {
            self.read_u32(Self::GSTS_REG)
        }
    }

    unsafe fn send_global_command(&mut self, offset: usize, value: bool) {
        let mut gcmd = self.global_status() & 0x96ffffff;
        gcmd.set_bit(offset, value);
        self.write_u32(Self::GCMD_REG, gcmd);

        loop {
            let gsts = self.global_status();
            if gsts.get_bit(offset) == value {
                break;
            }
            log::trace!("Waiting for command to be serviced");
        }
    }

    unsafe fn invalidate_context_cache(&mut self) {
        let mut ccmd = 0;
        ccmd.set_bit(Self::CCMD_ICC, true);
        ccmd.set_bits(Self::CCMD_CIRG, Self::CCMD_CIRG_GLOBAL);
        self.write_u64(Self::CCMD_REG, ccmd);
    }

    unsafe fn invalidate_iotlb(&mut self, bus: usize, device: usize, function: usize, page: u64) {
        let did = get_did(bus, device, function);

        let iro = 16 * self.ecap.get_bits(8..18);
        let iva_reg = iro as usize;
        let iotlb_reg = iro as usize + Self::IOTLB_REG_OFFSET;

        let mut iotlb_cmd: u64 = 0;
        iotlb_cmd.set_bit(Self::IOTLBCMD_IVT, true);
        iotlb_cmd.set_bits(Self::IOTLBCMD_DID, did as u64);

        let iirg = if page != 0 {
            Self::IOTLBCMD_IIRG_PAGE
        } else {
            Self::IOTLBCMD_IIRG_DOMAIN
        };

        iotlb_cmd.set_bits(Self::IOTLBCMD_IIRG, iirg);

        self.write_u64(iva_reg, PHYSICAL_PAGE_MASK & page);
        self.write_u64(iotlb_reg, iotlb_cmd);
    }

    pub fn enable_translation(&mut self) {
        unsafe {
            self.send_global_command(Self::GCMD_TE, true);
        }
    }

    pub fn disable_translation(&mut self) {
        unsafe {
            self.send_global_command(Self::GCMD_TE, false);
        }
    }

    pub unsafe fn set_root_table_addr(&mut self, address: u64) {
        self.write_u64(Self::RTADDR_REG, address);
        self.send_global_command(Self::GCMD_SRTP, true);

        if !self.cap.get_bit(Self::CAP_ESRTPS) {
            log::info!("Hardware supports ESRTPS");
        } else {
            log::info!("Hardware does not support ESRTPS");

            // > For implementations reporting the Enhanced Set Root Table Pointer Support (ESRTPS)
            // > field as Clear, on a ‘Set Root Table Pointer’ operation, software
            // > must perform a global invalidate of the context-cache,
            self.invalidate_context_cache();

            // > PASID-cache (if applicable),
            // not applicable to us

            // > and IOTLB, in that order.
            let iro = 16 * self.ecap.get_bits(8..18);
            let iotlb_reg = iro as usize + Self::IOTLB_REG_OFFSET;

            let mut iotlb_cmd = 0;
            iotlb_cmd.set_bit(Self::IOTLBCMD_IVT, true);
            iotlb_cmd.set_bits(Self::IOTLBCMD_IIRG, Self::IOTLBCMD_IIRG_GLOBAL);

            self.write_u64(iotlb_reg, iotlb_cmd);
        }
    }

    unsafe fn read_u32(&self, offset: usize) -> u32 {
        let p = (self.base as usize + offset) as *const u32;
        ptr::read_volatile(p)
    }

    unsafe fn write_u32(&self, offset: usize, value: u32) {
        let p = (self.base as usize + offset) as *mut u32;
        ptr::write_volatile(p, value);
    }

    unsafe fn read_u64(&self, offset: usize) -> u64 {
        let p = (self.base as usize + offset) as *const u64;
        ptr::read_volatile(p)
    }

    unsafe fn write_u64(&self, offset: usize, value: u64) {
        let p = (self.base as usize + offset) as *mut u64;
        ptr::write_volatile(p, value);
    }
}

impl NaiveIommuMap {
    pub const fn new() -> Self {
        Self {
            root_table: RootTable::new(),
            context_table: ContextTable::new(),
        }
    }

    pub fn root_table_addr(self: Pin<&mut Self>) -> u64 {
        //log::info!("Context Table: {:?}", &self.context_table as *const ContextTable);
        &self.root_table as *const RootTable as u64
    }

    pub fn map(mut self: Pin<&mut Self>, bus: usize, device: usize, function: usize, pml4: u64) {
        let did = get_did(bus, device, function);
        let re = RootTableEntry::new()
            .with_present(true)
            .with_address(&self.context_table as *const ContextTable as u64);

        let ce = ContextTableEntry::new()
            .with_present(true)
            .with_did(did)
            .with_address(pml4);

        unsafe {
            self.as_mut().root_table().write(bus, re);
            self.as_mut().context_table().write(device, function, ce);
        }

        for i in 0..256 {
            let e = unsafe { self.as_mut().root_table().as_ref().read(i) };
            log::debug!("bus {} = {:?}", i, e);
        }
        log::debug!("Setting IOPML4 to {:#x?}", pml4);
    }

    fn root_table<'a>(self: Pin<&'a mut Self>) -> Pin<&'a mut RootTable> {
        unsafe {
            self.map_unchecked_mut(|s| &mut s.root_table)
        }
    }

    fn context_table<'a>(self: Pin<&'a mut Self>) -> Pin<&'a mut ContextTable> {
        unsafe {
            self.map_unchecked_mut(|s| &mut s.context_table)
        }
    }
}

impl RootTable {
    const fn new() -> Self {
        Self {
            entries: [MaybeUninit::new(RootTableEntry::new()); 256],
        }
        //unsafe { mem::transmute(MaybeUninit::<Self>::zeroed()) }
    }

    unsafe fn read(self: Pin<&Self>, index: usize) -> RootTableEntry {
        assert!(index < self.entries.len(), "Out of range");
        ptr::read_volatile(self.entry(index))
    }

    unsafe fn write(self: Pin<&mut Self>, index: usize, value: RootTableEntry) {
        assert!(index < self.entries.len(), "Out of range");
        let e = self.entry_mut(index);
        log::info!("Index: {:#x}", index);
        log::info!("Writing to Root Table: {:?} <- {:#x?}", e, value);
        ptr::write_volatile(e, value);
    }

    fn entry(self: Pin<&Self>, index: usize) -> *const RootTableEntry {
        self.entries[index].as_ptr()
    }

    fn entry_mut(mut self: Pin<&mut Self>, index: usize) -> *mut RootTableEntry {
        self.entries[index].as_mut_ptr()
    }
}

impl ContextTable {
    const fn new() -> Self {
        Self {
            entries: [MaybeUninit::new(ContextTableEntry::new()); 256],
        }
    }

    #[allow(dead_code)]
    unsafe fn read(self: Pin<&Self>, device: usize, function: usize) -> ContextTableEntry {
        let index = Self::index(device, function);
        ptr::read_volatile(self.entry(index))
    }

    unsafe fn write(self: Pin<&mut Self>, device: usize, function: usize, value: ContextTableEntry) {
        let index = Self::index(device, function);
        let e = self.entry_mut(index);
        log::info!("Index: {:#x}", index);
        log::info!("Writing to Context Table: {:?} <- {:#x?}", e, value);
        ptr::write_volatile(e, value);
    }

    #[allow(dead_code)]
    fn entry(self: Pin<&Self>, index: usize) -> *const ContextTableEntry {
        self.entries[index].as_ptr()
    }

    fn entry_mut(mut self: Pin<&mut Self>, index: usize) -> *mut ContextTableEntry {
        self.entries[index].as_mut_ptr()
    }

    fn index(device: usize, function: usize) -> usize {
        assert!(device < 32, "Device out of range");
        assert!(function < 8, "Function out of range");

        (device << 3) | function
    }
}

impl RootTableEntry {
    const fn new() -> Self {
        Self {
            upper: 0,
            lower: 0,
        }
    }

    #[allow(dead_code)]
    fn present(&self) -> bool {
        (self.lower & 0b1) == 1
    }

    #[allow(dead_code)]
    fn address(&self) -> u64 {
        self.lower & PHYSICAL_PAGE_MASK
    }

    fn with_present(mut self, present: bool) -> Self {
        self.lower = (self.lower & !(0b1)) | (if present { 1 } else { 0 });
        self
    }

    fn with_address(mut self, address: u64) -> Self {
        let masked = PHYSICAL_PAGE_MASK & address;
        self.lower = self.lower & !(PHYSICAL_PAGE_MASK) | masked;
        self
    }
}

impl ContextTableEntry {
    const fn new() -> Self {
        // AW: 010b: 48-bit AGAW (4-level page table)
        let upper = 0b010;

        Self {
            upper,
            lower: 0,
        }
    }

    #[allow(dead_code)]
    fn present(&self) -> bool {
        (self.lower & 0b1) == 1
    }

    #[allow(dead_code)]
    fn address(&self) -> u64 {
        self.lower & PHYSICAL_PAGE_MASK
    }

    fn with_present(mut self, present: bool) -> Self {
        self.lower = (self.lower & !(0b1)) | (if present { 1 } else { 0 });
        self
    }

    fn with_did(mut self, did: u16) -> Self {
        let mut upper = self.upper;
        upper.set_bits(8..24, did as u64);
        self.upper = upper;
        self
    }

    fn with_address(mut self, address: u64) -> Self {
        let masked = PHYSICAL_PAGE_MASK & address;
        self.lower = self.lower & !(PHYSICAL_PAGE_MASK) | masked;
        self
    }
}

fn get_did(bus: usize, device: usize, function: usize) -> u16 {
    assert!(bus < 256, "Bus out of range");
    assert!(device < 32, "Device out of range");
    assert!(function < 8, "Function out of range");

    ((bus as u16) << 8) | ((device as u16) << 3) | (function as u16)
}

unsafe fn reload_root_table() {
    let rt = Pin::new(&mut NAIVE_MAP);
    let mut iommu = IOMMU.lock();
    let iommu = iommu.as_mut().expect("No IOMMU hardware");
    iommu.set_root_table_addr(rt.root_table_addr());
}

pub unsafe fn init_iommu() {
    let boot_info = crate::boot::get_boot_info();

    let mut iommu = if let Some(iommu_base) = boot_info.iommu_base {
        RemappingHardware::new(iommu_base)
    } else {
        return;
    };

    log::info!("Version: {:#x}", iommu.version());
    log::info!("Global Status: {:#x}", iommu.global_status());

    let rt = Pin::new(&mut NAIVE_MAP);
    iommu.set_root_table_addr(rt.root_table_addr());
    log::info!("Root Table: {:#x}", iommu.root_table_addr());

    log::info!("Enabling translation");
    iommu.enable_translation();

    *IOMMU.lock() = Some(iommu);
}

pub unsafe fn map(bus: usize, device: usize, function: usize, pml4: u64) -> Result<(), &'static str> {
    if IOMMU.lock().is_none() {
        return Err("No IOMMU available");
    }

    let rt = Pin::new(&mut NAIVE_MAP);
    rt.map(bus, device, function, pml4);

    // TODO: Reload device-specific context
    reload_root_table();

    Ok(())
}

pub unsafe fn invalidate_iotlb(bus: usize, device: usize, function: usize, page: u64) -> Result<(), &'static str> {
    let iommu = IOMMU.lock();

    let mut iommu = IOMMU.lock();
    let iommu = iommu.as_mut().ok_or("No IOMMU hardware")?;

    iommu.invalidate_iotlb(bus, device, function, page);

    Ok(())
}
