//! IOMMU.
//!
//! ## Glossary
//!
//! - PASID: Process Address Space Identifier that identifies the address space targeted by DMA requests.

use core::mem::{self, MaybeUninit};
use core::pin::Pin;
use core::ptr;

use bit_field::BitField;

const MAXPHYADDR: u64 = 56;
const PAGE_SZ: u64 = 4096;
const PAGE_MASK: u64 = !(PAGE_SZ - 1);
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

pub struct RemappingHardware {
    base: u64,
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
    const GCMD_REG: usize = 0x18;
    const RTADDR_REG: usize = 0x20;
    const GSTS_REG: usize = 0x1c;

    const CMD_TE: usize = 31;
    const CMD_SRTP: usize = 30;

    pub unsafe fn new(base: u64) -> Self {
        Self {
            base,
        }
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

    pub unsafe fn send_command(&mut self, offset: usize, value: bool) {
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

    pub fn enable_translation(&mut self) {
        unsafe {
            self.send_command(Self::CMD_TE, true);
        }
    }

    pub unsafe fn set_root_table_addr(&mut self, address: u64) {
        self.write_u64(Self::RTADDR_REG, address);
        self.send_command(Self::CMD_SRTP, true);
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
    pub fn new() -> Self {
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
        let re = RootTableEntry::new()
            .with_present(true)
            .with_address(&self.context_table as *const ContextTable as u64);

        let ce = ContextTableEntry::new()
            .with_present(true)
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
    fn new() -> Self {
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
    fn new() -> Self {
        Self {
            entries: [MaybeUninit::new(ContextTableEntry::new()); 256],
        }
    }

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

    fn present(&self) -> bool {
        (self.lower & 0b1) == 1
    }

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

    fn present(&self) -> bool {
        (self.lower & 0b1) == 1
    }

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
