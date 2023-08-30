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

use astd::io::Cursor;

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

    let kernel_image = boot::get_kernel_image().expect("No kernel image was passed");
    let kernel_image = Cursor::new(kernel_image);
    let elf = elf::ElfHandle::parse(kernel_image, 4096).unwrap();

    let mapping = elf.load(memory::memory()).unwrap();
    log::info!("Calling into kernel @ {:x?}", mapping.entry_point);

    let ret: usize;
    unsafe {
        asm!(
            // save state
            "mov r15w, ds; push r15w",
            "mov r15w, fs; push r15w",
            "mov r15w, gs; push r15w",
            "mov r15w, ss; push r15w",

            // clear state
            "xor rdi, rdi",
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

            inout("rax") mapping.entry_point => ret,
            out("rdi") _,
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
