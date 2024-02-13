//! Boot loader integration.

mod hvm;

use core::ptr;
use core::slice;

use crate::memory::MemoryRange;
use astd::heapless::Vec as ArrayVec;
use astd::sync::Mutex;

/// A list of kernel-usable memory regions.
static USABLE_MEMORY_REGIONS: Mutex<ArrayVec<MemoryRange, 100>> = Mutex::new(ArrayVec::new());

/// The memory region reserved for the initial allocator.
static RESERVED_MEMORY_REGION: Mutex<Option<MemoryRange>> = Mutex::new(None);

/// The kernel image passed by the bootloader.
static KERNEL_IMAGE: Mutex<Option<&'static [u8]>> = Mutex::new(None);

#[cfg(not(test))]
//#[link(name = "crt0")]
extern "C" {
    static bootinfo: u64;
    static __loader_start: u8;
    static __loader_end: u8;
}

#[cfg(test)]
static mut bootinfo: u64 = 0;

#[cfg(test)]
static mut __loader_start: u8 = 0;

#[cfg(test)]
static mut __loader_end: u8 = 0;

/// A type of bootloader.
#[derive(Debug)]
enum Bootloader {
    /// Multiboot 2.
    Multiboot2,

    /// Xen x86/HVM direct boot ABI.
    Hvm,
}

/// Returns the range of the loader itself.
pub fn get_loader_image_range() -> MemoryRange {
    let start = unsafe { &__loader_start as *const _ as u64 };
    let end_exclusive = unsafe { &__loader_end as *const _ as u64 };
    let size = end_exclusive - start;

    MemoryRange::new(start, size)
}

/// Initializes the boot loader information.
pub unsafe fn init() {
    let loader_range = get_loader_image_range();
    log::info!(
        "[ldr {:#016x}-{:#016x}]",
        loader_range.base(),
        loader_range.end_inclusive()
    );

    match detect_bootloader() {
        Some(Bootloader::Hvm) => {
            log::info!("Booted via Xen x86/HVM");

            let start_info =
                unsafe { hvm::StartInfo::load(bootinfo).expect("Invalid Xen x86/HVM start info") };
            start_info.dump_memmap();
            start_info.dump_modlist();

            let memory_regions: ArrayVec<MemoryRange, 100> = {
                let it = start_info
                    .iter_normal_memory_regions()
                    .filter(|range| !range.contains(0));

                ArrayVec::from_iter(it)
            };
            let occupied_regions: ArrayVec<MemoryRange, 100> = {
                let it = start_info
                    .iter_modlist()
                    .map(|module| module.to_memory_range());
                let mut vec = ArrayVec::from_iter(it);
                vec.push(get_loader_image_range()).unwrap();
                vec
            };
            // log::debug!("Occupied regions: {:#x?}", occupied_regions);

            let mut usable_regions = USABLE_MEMORY_REGIONS.lock();
            *usable_regions =
                crate::memory::compute_usable_memory_regions(&memory_regions, &occupied_regions);

            log::info!("Usable regions:");
            for region in usable_regions.iter() {
                log::info!(
                    "[mem {:#016x}-{:#016x}]",
                    region.base(),
                    region.end_inclusive()
                )
            }

            if let Some(module) = start_info.iter_modlist().next() {
                let mut kernel_image = KERNEL_IMAGE.lock();
                *kernel_image = Some(slice::from_raw_parts(
                    module.paddr as *const u8,
                    module.size as usize,
                ));
            }
        }
        Some(Bootloader::Multiboot2) => {
            log::info!("Booted via Multiboot2");
            unimplemented!();
        }
        _ => {
            panic!("Failed to detect bootloader, cannot continue");
        }
    }

    // Reserve region for bump allocator
    let reserve_size = 1024 * 1024 * 1024; // 1024 MiB
    let mut usable_regions = USABLE_MEMORY_REGIONS.lock();
    for usable_region in usable_regions.iter_mut() {
        if usable_region.size() > reserve_size {
            let mut reserved_region = RESERVED_MEMORY_REGION.lock();
            *reserved_region = Some(MemoryRange::new(usable_region.base(), reserve_size));
            *usable_region = MemoryRange::new(
                usable_region.base() + reserve_size,
                usable_region.size() - reserve_size,
            );
            log::debug!(
                "Reserved region for dynamic allocator: {:x?}",
                reserved_region
            );
            break;
        }
    }
}

pub fn get_reserved_region() -> Option<MemoryRange> {
    RESERVED_MEMORY_REGION.lock().clone()
}

pub fn get_kernel_image() -> Option<&'static [u8]> {
    KERNEL_IMAGE.lock().clone()
}

fn detect_bootloader() -> Option<Bootloader> {
    let bootinfo_addr = unsafe { bootinfo };

    if bootinfo_addr == 0 {
        return None;
    }

    let magic4 = {
        let magic_ptr = bootinfo_addr as *const u32;
        unsafe { ptr::read_unaligned(magic_ptr) }
    };

    if magic4 == hvm::HVM_START_INFO_MAGIC {
        Some(Bootloader::Hvm)
    } else {
        Some(Bootloader::Multiboot2)
    }
}
