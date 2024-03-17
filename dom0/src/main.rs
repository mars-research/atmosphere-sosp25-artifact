#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;
use core::arch::x86_64::_rdtsc;

#[start]
#[no_mangle]
fn main() -> isize {
    asys::init_logging();
    log::info!("hello {}", "world");

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
        // log::info!("sys_mmap {:?}", asys::sys_mmap(0xA000000000, 0x0000_0000_0000_0002u64 as usize, 20));
        // log::info!("sys_mresolve {:x?}", asys::sys_mresolve(0xA00000000F));
    }
    // test_new_send_no_wait();
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

fn test_new_send_no_wait(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let iter = 50000;
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty_no_wait(0);
                if error_code != 5 {
                    log::info!("sys_send_empty_no_wait failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("send no wait cycle per syscall {:?}",(end-start) as usize /iter);
        }
}

fn test_new_thread(){
    unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let iter = 249;
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_thread(0,0);
            if error_code != 0 {
                log::info!("sys_new_thread failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new thread cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

fn test_new_proc(){
    unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let iter = 4095;
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_proc(0,0);
            if error_code != 0 {
                log::info!("sys_new_proc failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new proc cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

fn test_new_endpoint(){
    let iter = 128;
    unsafe {
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_endpoint(i);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new endpoint cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

fn test_mmap(){
    let iter = 50000;
    unsafe {
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_mmap(0xA000000000 + 4096 * i, 0x0000_0000_0000_0002u64 as usize, 1);
            if error_code != 0 {
                log::info!("sys_mmap failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("mmap cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
