//! Boot loader integration.

mod hvm;

use core::ptr;
use core::slice;

use crate::memory::init_physical_memory_map;
use crate::memory::MemoryRange;
use astd::sync::Mutex;

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

            let regions = start_info
                .iter_memory_regions()
                .map(|(r, t)| (r, t.expect("Unknown memory type")));
            let loader_range = get_loader_image_range();
            let image_ranges = start_info
                .iter_modlist()
                .map(|module| module.to_memory_range());

            init_physical_memory_map(regions, loader_range, image_ranges);

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
