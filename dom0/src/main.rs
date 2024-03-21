#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;
use core::arch::x86_64::_rdtsc;
use core::arch::asm;

static mut array:[u8;4096] = [0;4096];

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
    // test_pingpong();
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

fn thread_1_main(){
    log::info!("hello from thread_1_main");
    // unsafe {
    //             log::info!("write {:x?}", (0xA000000000usize));
    //             *((0xA000000000usize) as *mut usize) = 0x233;
    //             log::info!("read {:x?}", (0xA000000000usize));
    //             let user_value = *((0xA000000000usize) as *const usize);
    //             log::info!("*{:x?} = {:x?}", (0xA000000000usize), user_value);
    //         }
    // unsafe {
    //     log::info!("write {:x?}", (0xA000001000usize));
    //     *((0xA000001000usize) as *mut usize) = 0x233;
    //     log::info!("read {:x?}", (0xA000001000usize));
    //     let user_value = *((0xA000001000usize) as *const usize);
    //     log::info!("*{:x?} = {:x?}", (0xA000001000usize), user_value);
    // }
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
            let error_code = asys::sys_new_thread(0,0,0);
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

fn test_pingpong(){
    log::info!("thread_1_main at {:p}", thread_1_main as *const ());
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let new_stack = 0xA000000000;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, 2);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        // log::info!("sys_mresolve sp {:x?}", asys::sys_mresolve(0x800ffff000));
        // log::info!("sys_mresolve new stack {:x?}", asys::sys_mresolve(new_stack));
        // unsafe {
        //     asm!(
        //         "mov rsp, {rsp}",
        //         rsp = inout(reg) new_stack => _,
        //     );
        // }
        // log::info!("hello from new rsp");

        let error_code = asys::sys_new_thread(0,thread_1_main as *const () as usize, ((&array as *const  u8 as u64) + 0x800)as usize);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
        let iter = 1;
        unsafe{
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty(0);
                log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_new_thread failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between threads using send/receive syscall {:?}",(end-start) as usize /iter);
        }

    }
    // log::info!("back to thread 0");
}


/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
