#![no_std]
#![no_main]
#![feature(start)]

use core::panic::PanicInfo;
use ring_buffer::*;
use core::ptr;

mod maglev;
mod slab_alloc;

use core::arch::x86_64::_rdtsc;
pub const DATA_BUFFER_ADDR: u64 = 0xF000000000;

use maglev::*;


#[start]
#[no_mangle]
fn main() {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello from maglev!");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by maglev");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..240 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }

        let iter = 500000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    // log::info!("pkt_op.unwrap().len {}", pkt_op.unwrap().len);
                    // log::info!("packet len {}", pkt_op.unwrap().len);
                    // let s = unsafe { core::slice::from_raw_parts(addr as *const u8, pkt_op.unwrap().len) };
                    // log::info!("{:x?}", s);

                    decode(addr as *mut u8);

                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
                    
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }

        }
        log::info!("warm up done");
        count = 0;

        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    decode(addr as *mut u8);
                            
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
                    
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }

        }

        let end = _rdtsc();

        log::info!("maglev cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop {}
}


/*
#[start]
#[no_mangle]
fn main() {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello from maglev!");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by maglev");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..240 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }

        let iter = 500000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0..32{
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    decode(addr as *mut u8);
                            
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
                    
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }
            asys::sys_receive_empty(0);
        }

        let end = _rdtsc();

        log::info!("maglev cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop {}
}
*/

pub unsafe fn decode(ptr :*mut u8){
    let header_len = 42;
    let head_len = 10;
    let command_len = 4;
    let c1 = *((ptr as usize + 42 + 10) as *mut u8);
    let c2 = *((ptr as usize + 42 + 11) as *mut u8);
    let c3 = *((ptr as usize + 42 + 12) as *mut u8);
    let c4 = *((ptr as usize + 42 + 13) as *mut u8);
    // log::info!("command {}{}{}{}", c1 as char, c2 as char, c3 as char, c4 as char);

    if c1 == b's' && c2 == b'e' && c3 == b't'{
        let key_start = (ptr as usize + 42 + 14) as *mut u8;
        let value_start = (ptr as usize + 42 + 14 + 11 + maglev::K_SIZE) as *mut u8;
        maglev_hashmap_insert(key_start, value_start);

        let set = b"STORED";

        ptr::copy(
            set.as_ptr(),
            ((ptr as usize + 42 + 10) as *mut u8),
            set.len(),
        );


    }else if c1 == b'g' && c2 == b'e' && c3 == b't'{
        let key_start = (ptr as usize + 42 + 14) as *mut u8;
        let pair = maglev_hashmap_get(key_start);
        let set = b"VALUE";

        ptr::copy(
            set.as_ptr(),
            ((ptr as usize + 42 + 10) as *mut u8),
            set.len(),
        );
        // log::info!("command {}{}{}{}", c1 as char, c2 as char, c3 as char, c4 as char);

    }

}

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
