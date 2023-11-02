//! The Atmosphere microkernel.
//!
//! See [`KernelCommandLine`](boot::command_line::KernelCommandLine) for a list of accepted kernel command-line options.

#![no_std]
#![feature(
    asm_const,
    abi_x86_interrupt,
    alloc_error_handler,
    arbitrary_self_types,
    const_mut_refs,
    custom_test_frameworks,
    naked_functions,
    pattern,
    start
)]
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
    deny(dead_code, unused_imports, unused_mut, unused_variables,)
)]
#![reexport_test_harness_main = "test_main"]
#![test_runner(crate::test_runner)]
#![no_main]

mod boot;
mod console;
mod cpu;
mod error;
mod gdt;
mod interrupt;
mod logging;
mod scripts;
mod utils;

use core::panic::PanicInfo;

use astd::boot::BootInfo;

static mut SHUTDOWN_ON_PANIC: bool = false;

/// CPU 0 entry point.
#[start]
#[no_mangle]
fn main(boot_info: *const BootInfo) -> isize {
    unsafe {
        console::early_init();
        logging::early_init();

        cpu::init_cpu0(); // Now get_current() can be used

        interrupt::init();
        interrupt::init_cpu();

        gdt::init_cpu();

        boot::init();
        console::init();
        logging::init();
    }

    let cmdline = boot::get_command_line();

    if !cmdline.nologo {
        print_logo();
    }

    log::info!("Command line: {}", boot::get_raw_command_line());
    #[cfg(debug_assertions)]
    {
        log::info!("Atmosphere was built in debug mode.");
    }

    #[cfg(test)]
    {
        log::info!("Atmosphere was built with the test harness");
        test_main();
    }

    unsafe {
        scripts::run_script_from_command_line();
        boot::spin_forever();
    }
}

/// Runs all tests.
#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) -> ! {
    unsafe {
        SHUTDOWN_ON_PANIC = true;
    }

    log::info!("Running {} tests", tests.len());

    for test in tests {
        test();
    }

    log::info!("All good!");

    unsafe {
        boot::shutdown(true);
    }
}

/// Prints the Atmosphere logo.
fn print_logo() {
    let logo = include_str!("logo.txt");
    for line in logo.split('\n') {
        log::info!("{}", line);
    }
}

/// The kernel panic handler.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("panic! {:#?}", info);

    unsafe {
        if SHUTDOWN_ON_PANIC {
            boot::shutdown(false);
        }
    }

    // FIXME: Signal all other CPUs to halt

    unsafe {
        boot::spin_forever();
    }
}
