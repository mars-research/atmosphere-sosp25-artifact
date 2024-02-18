//! The Atmosphere early loader.

#![cfg_attr(not(test), no_std, no_main, feature(start))]
#![feature(alloc_error_handler, strict_provenance, abi_x86_interrupt)]
#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_macros,
    unused_must_use,
    unused_unsafe
)]
#![deny(clippy::from_over_into, clippy::needless_question_mark)]
#![deny(rustdoc::bare_urls, rustdoc::broken_intra_doc_links)]
#![cfg_attr(
    not(debug_assertions),
    deny(dead_code, unused_imports, unused_mut, unused_variables)
)]

pub mod boot;
pub mod console;
pub mod elf;
pub mod logging;
pub mod memory;

use core::arch::asm;

#[cfg(not(test))]
use core::panic::PanicInfo;

use astd::boot::{BootInfo, DomainMapping};
use astd::io::{Cursor, Read, Seek, SeekFrom};

use elf::{ElfHandle, ElfMapping};
use memory::{AddressSpace, BootMemoryType, PhysicalAllocator};

const KERNEL_RESERVATION: usize = 256 * 1024 * 1024; // 256 MiB
const DOM0_RESERVATION: usize = 256 * 1024 * 1024; // 256 MiB
const PAGE_TABLE_RESERVATION: usize = 128 * 1024 * 1024; // 128 MiB
const PAGE_SIZE: usize = 4096;

/// Loader entry point.
#[cfg_attr(not(test), start, no_mangle)]
//#[no_mangle]
fn main(_argc: isize, _argv: *const *const u8) -> ! {
    unsafe {
        console::init();
        logging::init();
    }

    log::info!("** Atmosphere Loader **");

    unsafe {
        boot::init();
        memory::init();
    }

    let (_, mut page_table_allocator) = memory::reserve(PAGE_TABLE_RESERVATION, BootMemoryType::PageTable);
    let (_, mut kernel_allocator) = memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);

    let kernel_file = {
        let f = boot::get_kernel_image().expect("No kernel image was passed");
        Cursor::new(f)
    };

    let kernel_elf = ElfHandle::parse(kernel_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_end();

    let (kernel_map, mut kernel_file) = kernel_elf.load(&mut kernel_allocator).unwrap();

    // Also load dom0 if it exists
    kernel_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    let mut boot_info = BootInfo::empty(); // stays on stack

    match load_domain(kernel_file, &kernel_map, &mut page_table_allocator) {
        Ok(dom0) => {
            boot_info.dom0 = Some(dom0);
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    memory::dump_physical_memory_map();

    log::info!("Calling into kernel @ {:x?}", kernel_map.entry_point);

    let ret: usize;
    unsafe {
        asm!(
            // save state
            "mov r15w, ds; push r15w",
            "mov r15w, fs; push r15w",
            "mov r15w, gs; push r15w",
            "mov r15w, ss; push r15w",

            // clear state
            // rdi = &boot_info
            "xor rsi, rsi",
            "xor r15, r15",
            "mov ds, r15w",
            "mov fs, r15w",
            "mov gs, r15w",
            "mov ss, r15w",

            // call entry
            "call rax",

            // restore state
            "pop r15w; mov ss, r15w",
            "pop r15w; mov gs, r15w",
            "pop r15w; mov fs, r15w",
            "pop r15w; mov ds, r15w",

            inout("rax") kernel_map.entry_point => ret,
            inout("rdi") &boot_info as *const _ => _,
            out("rsi") _,
            out("r15") _,
        );
    }

    log::info!("Returned from kernel: 0x{:x}", ret);

    loop {}
}

fn load_domain<T>(elf: T, kernel_map: &ElfMapping, page_table_allocator: &mut impl PhysicalAllocator) -> Result<DomainMapping, elf::Error>
    where
        T: Read + Seek,
        T::Error: Into<elf::Error>,
{
    let parsed = ElfHandle::parse(elf, PAGE_SIZE)?;
    log::info!("Loading Dom0...");

    // TODO: Relocate to fixed virtual address
    let (reserved_start, mut memory) = memory::reserve(DOM0_RESERVATION, BootMemoryType::Domain); // FIXME: Use AddressSpace as allocator
    let (dom_map, _) = parsed.load(&mut memory).expect("Failed to map Dom0");

    let mut address_space = AddressSpace::new(page_table_allocator);

    log::info!("Mapping Dom0 pages...");
    let mut cur = reserved_start;
    while cur.addr() < reserved_start.addr() + DOM0_RESERVATION {
        unsafe {
            address_space.map(cur as u64, cur as u64, true);
            cur = cur.add(PAGE_SIZE);
        }
    }

    // Set up kernel mapping
    let mut cur = kernel_map.load_bias;
    while cur < kernel_map.max_vaddr {
        unsafe {
            address_space.map(cur as u64, cur as u64, false);
            cur = cur + PAGE_SIZE;
        }
    }

    // Set up system mapping
    let mut cur = 0x0;
    while cur < 1 * 1024 * 1024 {
        unsafe {
            address_space.map(cur as u64, cur as u64, false);
            cur = cur + PAGE_SIZE;
        }
    }

    Ok(DomainMapping {
        reserved_start,
        reserved_size: DOM0_RESERVATION,
        entry_point: dom_map.entry_point,
        pml4: address_space.pml4(),
        load_bias: dom_map.load_bias,
    })
}

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}
