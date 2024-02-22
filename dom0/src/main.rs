#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;

#[start]
#[no_mangle]
fn main() -> isize {
    asys::init_logging();
    log::info!("hello {}", "world");

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
    }

    loop {}
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
