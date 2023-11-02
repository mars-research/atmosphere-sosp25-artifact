#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;

#[start]
#[no_mangle]
fn main() -> isize {
    42
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
