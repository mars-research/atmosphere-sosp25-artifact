//! The Atmosphere early loader.

#![no_std]
#![no_main]
#![feature(start, alloc_error_handler, strict_provenance, abi_x86_interrupt)]
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
use astd::io::{Cursor, Seek, SeekFrom};

use elf::ElfHandle;

const DOM0_RESERVATION: usize = 128 * 1024 * 1024; // 128 MiB

/// Loader entry point.
#[start]
#[no_mangle]
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

    let kernel_file = {
        let f = boot::get_kernel_image().expect("No kernel image was passed");
        Cursor::new(f)
    };

    let kernel_elf = ElfHandle::parse(kernel_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_end();

    let (kernel_map, mut kernel_file) = kernel_elf.load(memory::memory()).unwrap();

    // Also load dom0 if it exists
    kernel_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    let mut boot_info = BootInfo::empty(); // stays on stack

    match ElfHandle::parse(kernel_file, 4096) {
        Ok(dom0_elf) => {
            log::info!("Loading Dom0...");

            let (reserved_start, mut memory) = memory::reserve(DOM0_RESERVATION);
            let (dom0_map, _) = dom0_elf.load(&mut memory).expect("Failed to map Dom0");

            let dom0 = DomainMapping {
                reserved_start,
                reserved_size: DOM0_RESERVATION,
                entry_point: dom0_map.entry_point,
                load_bias: dom0_map.load_bias,
            };
            log::info!("Loaded Dom0: {:?}", dom0);

            boot_info.dom0 = Some(dom0);
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

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

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}
