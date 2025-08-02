#![no_std]
#![no_main]
#![feature(start)]

extern crate alloc;
// extern crate ixgbe_driver;
extern crate nvme_driver;
extern crate pcid;
extern crate ring_buffer;

// mod ixgbe_client;
mod nvme_client;
mod pci;
mod slab_alloc;
// mod elf;
// mod dom1;
// mod maglev;
// mod smoltcp_device;

use core::panic::PanicInfo;
// mod benchmark_null_driver;
mod syscall_benchmark;
use alloc::vec::Vec;
// use ixgbe_client::*;
use libtime::sys_ns_loopsleep;
pub use log::info as println;
use nvme_client::*;
use pci::scan_pci_devs;
use constants::*;
use syscall_benchmark::*;

fn test_sleep() {
    log::trace!("Sleeping for 100 ns");
    sys_ns_loopsleep(100);
    log::trace!("Waking up from sleep");
}

fn test_alloc() {
    log::info!("testing alloc");
    let mut v: Vec<u64> = Vec::with_capacity(32);
    for i in 0..64 {
        v.push(i);
    }
    log::info!("Allocator works");
}

#[start]
#[no_mangle]
extern "C" fn main(payload_base: *mut u8, payload_size: usize) -> isize {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::trace!("hello {}", "world");
    log::info!("payload {:?}, size {}", payload_base, payload_size);

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
    }
    log::info!("Enumerating PCI");
    scan_pci_devs();
    test_nvme_with_ring_buffer();

    loop {}
}
fn thread_1_main() {
    log::info!("hello from thread_1_main");
    loop {
        unsafe {
            log::info!("ping");
            let error_code = asys::sys_send_empty_try_schedule(0);
            if error_code != 0 {
                log::info!("sys_new_thread failed {:?}", error_code);
                return;
            }
        }
    }
}

// fn thread_1_hello_ap() {
//     log::info!("hello from thread_1_main");
// }

fn dom_1_main() {
    log::info!("hello from dom_1_main");
    loop {
        unsafe {
            // log::info!("ping");
            let error_code = asys::sys_send_empty_try_schedule(0);
            if error_code != 0 {
                log::info!("sys_send_empty_try_schedule failed {:?}", error_code);
                return;
            }
        }
    }
}

/// The kernel panic handler.
#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
