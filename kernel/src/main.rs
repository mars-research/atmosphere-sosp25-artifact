#![feature(start)]
#![no_std]
#![no_main]

#[no_mangle]
fn main() -> usize {
    42
}

#[cfg(not(test))]
#[panic_handler]
fn panic_handler(info: &core::panic::PanicInfo) -> ! {
    loop {}
}