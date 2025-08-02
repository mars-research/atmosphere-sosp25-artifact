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
    // test_mmap();
    // test_pingpong();
    // test_proc_pingpong();

    // unsafe {
    //     let io_cr3 = asys::sys_rd_io_cr3();
    //     log::info!("Dom0 IOMMU table @ {:x}", io_cr3);
    //     let error_code = asys::sys_io_mmap(IOMMU_TEST_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, 1);
    //     if error_code != 0 {
    //         log::debug!("sys_io_mmap for IOMMU_TEST_ADDR failed {:?}", error_code);
    //     }
    //     log::info!("IOMMU table reslove {:x}",asys::sys_mresolve_io(IOMMU_TEST_ADDR as usize).0 as u64);
    // }
    //     log::info!("Dom0 IOMMU table @ {:x}", io_cr3);
    //     let error_code = asys::sys_mmap(IOMMU_TEST_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, 1);
    //     if error_code != 0 {
    //         log::info!("sys_mmap for IOMMU_TEST_ADDR failed {:?}", error_code);
    //         // return;
    //     }
    //     let error_code = asys::sys_io_mmap(IOMMU_TEST_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, 1);
    //     if error_code != 0 {
    //         log::info!("sys_io_mmap for IOMMU_TEST_ADDR failed {:?}", error_code);
    //         // return;
    //     }
    //     log::info!("Pagetable reslove {:x}",asys::sys_mresolve(IOMMU_TEST_ADDR as usize).0 as u64);
    //     log::info!("IOMMU table reslove {:x}",asys::sys_mresolve_io(IOMMU_TEST_ADDR as usize).0 as u64);
    // }
    // if !payload_base.is_null() {
    //     let payload = unsafe {
    //         slice::from_raw_parts(payload_base, payload_size)
    //     };

    //     dom1::spawn_dom1(payload);
    // }
    // dom1::spawn_dom1();

    // test_proc_pingpong();

    // test_sleep();

    // test_alloc();

    log::info!("Enumerating PCI");

    scan_pci_devs();

    // start_ixgbe_driver_fwd_test();

    // // test_ixgbe_with_ring_buffer_tx();

    // // test_ixgbe_driver();
    // test_nvme_driver();
    // test_nvme_with_ring_buffer();
    test_nvme_pingpong();
    // unsafe {
    //     let error_code = asys::sys_new_endpoint(0);
    //     if error_code != 0 {
    //             log::info!("sys_new_endpoint failed {:?}", error_code);
    //         }
    //     let new_stack = 0xA000000000;
    //     let size = 16 * 1024 * 1024;
    //     let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
    //     if error_code != 0 {
    //         log::info!("sys_mmap failed {:?}", error_code);
    //     }

    //     let rsp: usize = (new_stack + size) & !(4096 - 1);
    //     let error_code = asys::sys_new_thread(0,thread_1_main as *const () as usize, rsp);
    //     if error_code != 0 {
    //         log::info!("sys_new_thread failed {:?}", error_code);
    //     }
    // }
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
