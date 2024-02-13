#![no_std]
#![no_main]
#![feature(start)]

use core::arch::asm;
use core::panic::PanicInfo;

#[start]
#[no_mangle]
fn main() -> isize {
    unsafe {
        asm!(
            "syscall",
            "2:",
            //"hlt",
            "jmp 2b",
        );
    }
    42
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
