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
        log::info!("sys_mmap {:?}", asys::sys_mmap(0xA000000000, 0x0000_0000_0000_0002u64 as usize, 20));
        log::info!("sys_mresolve {:x?}", asys::sys_mresolve(0xA00000000F));
    }
    // for i in 0..20{
    //     let mut user_value: usize = 0;
    //     unsafe {
    //         log::info!("write {:x?}", (0xA000000000usize + i * 4096));
    //         *((0xA000000000usize + i * 4096) as *mut usize) = 0x233;
    //         log::info!("read {:x?}", (0xA000000000usize + i * 4096));
    //         user_value = *((0xA000000000usize + i * 4096) as *const usize);
    //     }
    //     log::info!("*{:x?} = {:x?}", (0xA000000000usize + i * 4096), user_value);
    // }

    loop {}
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
