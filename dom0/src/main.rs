#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;
use core::arch::x86_64::_rdtsc;
use core::arch::asm;
mod ring_buffer;
use crate::ring_buffer::*;

pub const data_buffer_addr:u64 = 0xF000000000;

#[start]
#[no_mangle]
fn main() -> isize {
    asys::logger::init_logging_with_level(log::Level::Trace);
    log::trace!("hello {}", "world");

    unsafe {
        asys::sys_print("meow".as_ptr(), 4);
    }
    // test_null_driver();

    loop {}
}

#[no_mangle]
fn test_null_driver_ap()->!{
    log::info!("hello from test_null_driver_ap");

    unsafe{
        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_receive_pages(0,data_buffer_addr as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   
    }

    let target = 10000000;
    let mut counter = 0;
        unsafe{
            let buff_ref:&mut DataBufferAllocWrapper = &mut*(data_buffer_addr as *mut DataBufferAllocWrapper);
            for i in 0..size_of_queue{
                buff_ref.free_stack[buff_ref.len] = i;
                buff_ref.len = buff_ref.len + 1;
            }
            // log::info!("free_stack init done");
            let start = _rdtsc();
            while counter <= target{
                //push free stack into request queue
                // log::info!("counter: {:?}",counter);
                while buff_ref.len != 0{
                    let result = buff_ref.request_queue.try_push(buff_ref.free_stack[buff_ref.len-1]);
                    // log::info!("result: {:?} i: {:?}",result,free_stack[len-1]);
                    if result{
                        buff_ref.len = buff_ref.len -1;
                    }
                    

                }
                //pop reply queue to free stack
                loop{
                    let result = buff_ref.reply_queue.try_pop();
                    if result.is_none(){
                        break;
                    }else{
                        counter = counter + 1;
                        buff_ref.free_stack[buff_ref.len] = result.unwrap();
                        buff_ref.len = buff_ref.len + 1;
                    }
                }
            }
            let end = _rdtsc();
            log::info!("null_driver cycles per request {:?}",(end-start) as usize /target);
        }

    loop {
        unsafe{asm!("nop");}
    }
}
fn test_null_driver(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 34{
                break;
            }
            range = range + 1;
        }
        log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }
        let rsp: usize = new_stack + size/2;
        log::info!("request_queue address: {:x?}", rsp);  
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_null_driver_ap as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        // log::info!("request_queue address: {:p}", &request_queue);   

        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_mmap(data_buffer_addr as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut DataBufferAllocWrapper = &mut*(data_buffer_addr as *mut DataBufferAllocWrapper);
        buff_ref.init();
        log::info!("data_buffer init done");

        loop{
            let error_code = asys::sys_send_pages_no_wait(0,data_buffer_addr as usize, size / 4096 + 1);
            if error_code == 5  {
            }else{
                if error_code == 0{
                    log::info!("data_buffer sent to dom1");
                    break;
                }else{
                    log::info!("sys_send_pages_no_wait failed {:?}", error_code);
                    break;
                }
            }
        }
        loop{
            let result = buff_ref.request_queue.try_pop();
            if result.is_none(){
                for i in 0..100{
                    asm!("nop");
                }
            }else{
                // for i in 0..size_of_buffer{
                //     buff_ref.data_buffer[result.unwrap()][i] += 1;
                // }
                buff_ref.reply_queue.try_push(result.unwrap());
            }
        }
    }
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

fn try_new_thread_ap(){
    log::info!("thread_1_hello_ap at {:p}", thread_1_hello_ap as *const ());
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let new_stack = 0xA000000000;
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        let rsp: usize = (new_stack + size) & !(4096 - 1);

        let error_code = asys::sys_new_thread(0,thread_1_hello_ap as *const () as usize, rsp);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
    }
}

fn test_proc_pingpong(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 34{
                break;
            }
            range = range + 1;
        }
        log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }
        let rsp: usize = (new_stack + size) & !(4096 - 1);
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,dom_1_main as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }

        let iter = 100000;
        unsafe{
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty(0);
                // log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_send_empty failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between process using send/receive syscall {:?}",(end-start) as usize /iter);
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
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        let rsp: usize = (new_stack + size) & !(4096 - 1);

        let error_code = asys::sys_new_thread(0,thread_1_main as *const () as usize, rsp);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
        let iter = 100000;
        unsafe{
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty(0);
                // log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_new_thread failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between threads using send/receive syscall {:?}",(end-start) as usize /iter);
        }

    }
}


/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
