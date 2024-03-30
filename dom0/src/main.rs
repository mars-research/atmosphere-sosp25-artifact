#![no_std]
#![no_main]
#![feature(start, asm_const)]

extern crate alloc;
extern crate nvme_driver;
extern crate pcid;

mod pci;
mod slab_alloc;

use core::arch::asm;
use core::arch::x86_64::_rdtsc;
use core::panic::PanicInfo;
mod benchmark_null_driver;
mod ring_buffer;
mod syscall_benchmark;
use crate::benchmark_null_driver::*;
use crate::ring_buffer::*;
use crate::syscall_benchmark::*;
use alloc::vec::Vec;
use libtime::sys_ns_loopsleep;
pub use log::info as println;
use nvme_driver::device::NvmeDevice;
use pci::scan_pci_devs;
use pcid::utils::PciBarAddr;

pub const DATA_BUFFER_ADDR: u64 = 0xF000000000;
pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

fn test_sleep() {
    log::trace!("Sleeping for 100 ns");
    sys_ns_loopsleep(100);
    log::trace!("Waking up from sleep");
}

fn test_alloc() {
    let mut v: Vec<u64> = Vec::with_capacity(32);
    for i in 0..64 {
        v.push(i);
    }
}

#[start]
#[no_mangle]
fn main() -> isize {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::trace!("hello {}", "world");

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
    }
    // test_proc_pingpong();

    test_sleep();

    test_alloc();

    log::info!("Enumerating PCI");

    scan_pci_devs();

    log::info!("Running Nvme test");

    let mut nvme_dev =
        unsafe { NvmeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xfebf_0000, 0x4000)) };

    nvme_dev.init();

    nvme_driver::nvme_test::run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, true, false, 0);
    nvme_driver::nvme_test::run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, false, false, 0);

    loop {}
}
fn thread_1_main() {
    log::info!("hello from thread_1_main");
    loop {
        unsafe {
            // log::info!("ping");
            let error_code = asys::sys_receive_empty(0);
            if error_code != 0 {
                log::info!("sys_new_thread failed {:?}", error_code);
                return;
            }
        }
    }
}

fn thread_1_hello_ap() {
    log::info!("hello from thread_1_main");
}

fn dom_1_main() {
    log::info!("hello from dom_1_main");
    loop {
        unsafe {
            // log::info!("ping");
            let error_code = asys::sys_receive_empty(0);
            if error_code != 0 {
                log::info!("sys_receive_empty failed {:?}", error_code);
                return;
            }
        }
    }
}

/// The kernel panic handler.
#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
