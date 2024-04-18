//! ACPI.

use core::ptr;
use core::mem;
use core::pin::Pin;

use acpi::{AcpiTables, AcpiTable, PhysicalMapping};
use acpi::handler::AcpiHandler;
use acpi::sdt::{Signature, SdtHeader};

use crate::iommu::{NaiveIommuMap, RemappingHardware};
use crate::memory::{self, PhysicalAllocator, AddressSpace};

#[derive(Clone, Debug)]
struct NullAcpiHandler {}

#[derive(Debug)]
#[repr(C, packed)]
struct Dmar {
    header: SdtHeader,

    host_address_width: u8,
    flags: u8,
    _reserved: [u8; 10],
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct RemappingHeader {
    struct_type: u16,
    length: u16,
}

#[derive(Debug)]
struct RemappingPtrIter {
    cur: *const u8,
    limit: *const u8,
}

/// DMA Remapping Hardware Unit Definition
///
/// Section 8.3
#[derive(Debug)]
#[repr(C, packed)]
struct Drhd {
    header: RemappingHeader,
    flags: u8,
    size: u8,
    segment_number: u16,
    register_base_address: u64,
}

impl NullAcpiHandler {
    fn new() -> Self {
        Self {}
    }
}

impl AcpiHandler for NullAcpiHandler {
    unsafe fn map_physical_region<T>(&self, physical_address: usize, size: usize) -> PhysicalMapping<Self, T> {
        let p = ptr::NonNull::new_unchecked(physical_address as *mut T);
        PhysicalMapping::new(
            physical_address,
            p,
            size,
            size,
            self.clone(),
        )
    }

    fn unmap_physical_region<T>(_region: &PhysicalMapping<Self, T>) {
        // no-op
    }
}

impl Dmar {
    fn iter_remapping_structs(&self) -> RemappingPtrIter {
        let entries_length = self.header.length as usize - mem::size_of::<Self>();
        let start = unsafe {
            (self as *const Self).add(1) as *const u8
        };
        let limit = unsafe {
            start.add(entries_length)
        };
        RemappingPtrIter {
            cur: start,
            limit,
        }
    }
}

unsafe impl AcpiTable for Dmar {
    const SIGNATURE: Signature = Signature::DMAR;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

impl Iterator for RemappingPtrIter {
    type Item = &'static RemappingHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur >= self.limit {
            return None;
        }

        let header = unsafe {
            &*(self.cur as *const RemappingHeader)
        };
        self.cur = unsafe {
            self.cur.add(header.length as usize)
        };

        log::info!("Header: {:?}", header);

        Some(header)
    }
}

impl RemappingHeader {
    const TYPE_DRHD: u16 = 0;

    fn as_drhd<'a>(&self) -> Option<&'a Drhd> {
        if self.struct_type != Self::TYPE_DRHD {
            return None;
        }

        let p = self as *const RemappingHeader as *const Drhd;
        let r = unsafe { &*p };
        Some(r)
    }
}

pub fn init_acpi(addr_space: AddressSpace) {
    let handler = NullAcpiHandler::new();
    let acpi = unsafe {
        AcpiTables::search_for_rsdp_bios(handler).expect("failed to find RSDP")
    };

    log::info!("ACPI: {:?}", acpi);

    let dmar = if let Ok(dmar) = acpi.find_table::<Dmar>() {
        dmar
    } else {
        log::warn!("No DMAR table available - Skipping IOMMU init");
        return;
    };

    log::info!("DMAR: {:#?}", *dmar);

    let drhde = dmar.iter_remapping_structs().find_map(|header| {
        header.as_drhd()
    }).expect("failed to find DRHD entry");

    let mut drhd = unsafe {
        RemappingHardware::new(drhde.register_base_address)
    };
    log::info!("Version: {:#x}", drhd.version());
    log::info!("Global Status: {:#x}", drhd.global_status());
    log::info!("Root Table: {:#x}", drhd.root_table_addr());

    let mut naive_table = unsafe {
        let p = memory::bootstrap_allocator().allocate_physical(mem::size_of::<NaiveIommuMap>());
        let pp = p.0 as *mut NaiveIommuMap;
        ptr::write(pp, NaiveIommuMap::new());
        Pin::new(&mut *pp)
    };

    let pml4: u64;
    unsafe {
        core::arch::asm!("mov {}, cr3", out(reg) pml4);
    }
    log::info!("Mapping PML4 {:>08x}", pml4);
    naive_table.as_mut().map(0x00, 0x03, 0x00, pml4);
    //naive_table.as_mut().map(0x00, 0x03, 0x00, addr_space.pml4() as u64);

    unsafe {
        drhd.set_root_table_addr(naive_table.root_table_addr() as u64);
    }
    drhd.enable_translation();
    log::info!("Global Status: {:#x}", drhd.global_status());
    log::info!("Root Table: {:#x}", drhd.root_table_addr());
}
