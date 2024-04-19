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
// #![cfg_attr(
//     not(debug_assertions),
//     deny(dead_code, unused_imports, unused_mut, unused_variables,)
// )]
#![reexport_test_harness_main = "test_main"]
#![test_runner(crate::test_runner)]
#![no_main]

mod boot;
mod bridge;
mod console;
mod cpu;
mod debugger;
mod error;
mod gdt;
mod interrupt;
mod iommu;
mod kernel;
mod logging;
mod scripts;
mod syscalls;
mod thread;
mod utils;
mod ring_buffer;

use core::arch::asm;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::{ffi::c_void, panic::PanicInfo};

use astd::boot::{BootInfo, PhysicalMemoryType};
use x86::Ring;

static mut SHUTDOWN_ON_PANIC: bool = false;

static mut AP_STACK: [u8; 64 * 1024 * 1024] = [0; 64 * 1024 * 1024];
static mut THREAD_STACK: [u8; 64 * 1024 * 1024] = [0; 64 * 1024 * 1024];
static THREAD_COUNTER: AtomicUsize = AtomicUsize::new(0);

use verified::array_vec::ArrayVec as vArrayVec;

/// CPU 0 entry point.
#[start]
#[no_mangle]
fn main(boot_info: *const BootInfo) -> isize {
    unsafe {
        console::early_init();
        logging::early_init();

        cpu::init_cpu(0); // Now get_current() can be used
        gdt::init_cpu();

        interrupt::init();
        interrupt::init_cpu();

        syscalls::init_cpu();

        boot::init(boot_info);
        iommu::init_iommu();

        // XXX: disable reinitializing console as it hangs on real hw. disabling it on qemu doesn't
        // cause any harm
        //console::init();
        logging::init();
    }

    let cmdline = boot::get_command_line();

    if !cmdline.nologo {
        print_logo();
    }

    // Thread test
    // unsafe {
    //     thread::start_thread(
    //         thread_main as u64,
    //         &THREAD_STACK as *const _ as u64 + THREAD_STACK.len() as u64,
    //         Ring::Ring0,
    //     );
    // }
    // loop {
    //     let counter = THREAD_COUNTER.load(Ordering::SeqCst);
    //     log::debug!("Counter: {}", counter);
    // }


    kernel::kernel_test();
    kernel::kernel_new();

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

    let boot_info = boot::get_boot_info();
    let dom0 = boot_info.dom0.as_ref().unwrap();
    let pml4 = boot_info.pml4;
    let mut kernel_pml4: usize = 0;
    unsafe {
        kernel_pml4 = *(pml4 as *const usize);
    }
    log::info!("dom0: {:?}", dom0);
    log::info!("pml4: {:?}", pml4);
    log::info!("kernel_pml4: {:x}", kernel_pml4);
    log::info!("page_array_len: {:x}", boot_info.pages.len());

    kernel::kernel_init(&boot_info.pages, pml4 as usize, kernel_pml4 as usize);

    // unsafe {
    //     let ap_rsp = (&AP_STACK as *const _ as u64 + AP_STACK.len() as u64) & !(4096 - 1);
    //     interrupt::boot_ap(
    //         1,
    //         ap_rsp,
    //         ap_main as u64,
    //     );
    // }

    let initial_sp = unsafe { dom0.virt_start.add(dom0.reserved_size - 0x1000) };
    log::info!("initial_sp: {:?}", initial_sp);
    unsafe {
        let (rdi, rsi) = if let Some(payload) = &boot_info.payload {
            (payload.base as u64, payload.size as u64)
        } else {
            (0, 0)
        };

        enter_userspace(dom0.entry_point, initial_sp as *mut _, rdi, rsi);
    }

    unsafe {
        scripts::run_script_from_command_line();
        boot::spin_forever();
    }
}

/// AP entry point.
fn ap_main(cpu_id: u64, rsp: u64) {
    unsafe {
        cpu::init_cpu(cpu_id as usize);
        gdt::init_cpu();
        interrupt::init_cpu();
        syscalls::init_cpu();
    }

    // log::info!("Hello from CPU {}", cpu::get_cpu_id());

    unsafe {
        thread::start_thread(
            thread_main as u64,
            (&THREAD_STACK as *const _ as u64 + THREAD_STACK.len() as u64) & !(4096 - 1),
            Ring::Ring3,
        );
    }

    loop {
    }
}

/// Thread entry point.
fn thread_main(cpu_id: u64) {
    //debugger::breakpoint(1);
    loop {
        THREAD_COUNTER.fetch_add(1, Ordering::SeqCst);
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

    debugger::breakpoint(1);

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

unsafe fn enter_userspace(pc: *const c_void, sp: *mut c_void, rdi: u64, rsi: u64) -> ! {
    log::info!("Going to sysret into {:x?}", pc);
    asm!(
        "pushfq",
        "pop r11",
        "mov rsp, {sp}",
        // HACK: Set IOPL to 3 unconditionally for accessing io ports from dom0
        "or r11, (3 << 12)",
        "sysretq",

        in("rcx") pc,
        sp = in(reg) sp,
        in("rdi") rdi,
        in("rsi") rsi,
        out("r15") _,
    );

    loop {}
}
