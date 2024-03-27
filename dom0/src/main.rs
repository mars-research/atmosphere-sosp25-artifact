#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;
use core::arch::x86_64::_rdtsc;
use core::arch::asm;
mod syscall_benchmark;
mod benchmark_null_driver;
mod ring_buffer;
use crate::ring_buffer::*;
use crate::benchmark_null_driver::*;
use crate::syscall_benchmark::*;
use libtime::sys_ns_loopsleep;

pub const DATA_BUFFER_ADDR:u64 = 0xF000000000;

#[start]
#[no_mangle]
fn main() -> isize {
    asys::logger::init_logging_with_level(log::Level::Trace);
    log::trace!("hello {}", "world");

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
    }
    // test_proc_pingpong();

    sys_ns_loopsleep(100);
    loop {}
}
fn thread_1_main(){
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

fn thread_1_hello_ap(){
    log::info!("hello from thread_1_main");
}

fn dom_1_main(){
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