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

    maglev_init();

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
                    let backend = maglev_process_frame(addr as *mut rte_ether_hdr, pkt_op.unwrap().len);
                    log::info!("packet len {}", pkt_op.unwrap().len);
                    let s = unsafe { core::slice::from_raw_parts(addr as *const u8, pkt_op.unwrap().len) };
                    log::info!("{:x?}", s);

                    if backend != 233{
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
        
                            
                    let backend = maglev_process_frame(addr as *mut rte_ether_hdr, pkt_op.unwrap().len);
                    if backend != 233{
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

// #[start]
// #[no_mangle]
// fn main() {
//     asys::logger::init_logging_with_level(log::Level::Info);
//     log::info!("Hello from maglev!");

//     let sender_mac = [
//         0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
//     ];
//     let our_mac = [
//         // 90:E2:BA:B5:15:75
//         0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
//     ];

//     maglev_init();

//     unsafe{
//         let size = core::mem::size_of::<IxgbeRingBuffer>();
//         let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
//         if error_code != 0 {
//             log::info!("sys_receive_pages failed {:?}", error_code);
//         }else{
//             log::info!("data_buffer received by maglev");
//         }   

//         let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

//         for i in 0..240 {
//             let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
//             buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
//             // log::info!("receiving package at {:x}", addr);
//         }

//         let iter = 500000000;
//         let mut count = 0;
//         let print_iter = iter/20;
//         let mut print_count = 0;

//         let start = _rdtsc();

//         while count <= iter {

//             for i in 0..32{
//                 if print_count >= print_iter{
//                     log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
//                     print_count = 0;
//                 }
//                     let pkt_op = buff_ref.request_completion_queue.try_pop();
//                     if pkt_op.is_none(){
//                         break;
//                     }else{
//                         // log::info!("received package at {:x}", pkt_op.unwrap().addr);
        
//                         count = count + 1;
//                         print_count = print_count + 1;
//                         let addr = pkt_op.unwrap().addr;
            
                                
//                         let backend = maglev_process_frame(addr as *mut rte_ether_hdr, pkt_op.unwrap().len);
//                         if backend != 233{
//                             unsafe {
//                                 ptr::copy(
//                                     our_mac.as_ptr(),
//                                     (addr + 6) as *mut u8,
//                                     our_mac.len(),
//                                 );
//                                 ptr::copy(
//                                     sender_mac.as_ptr(),
//                                     addr as *mut u8,
//                                     sender_mac.len(),
//                                 );
//                             }
//                         }
//                         buff_ref.reply_queue.try_push(&pkt_op.unwrap());
//                         // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
//                     }
//             }
//             asys::sys_receive_empty(0);
//         }

//         let end = _rdtsc();

//         log::info!("maglev cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
//     }
//     loop {}
// }

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
