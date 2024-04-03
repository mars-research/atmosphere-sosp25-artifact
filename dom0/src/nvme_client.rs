extern crate nvme_driver;
extern crate ring_buffer;
use crate::USERSPACE_BASE;
use core::mem::MaybeUninit;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::{run_blocktest_blkreq, run_blocktest_raw_with_delay};
use pcid::utils::PciBarAddr;
use crate::ring_buffer::{RingBuffer, SIZE_OF_BUFFER, SIZE_OF_QUEUE};
use nvme_driver::*;
use core::arch::asm;
use crate::DATA_BUFFER_ADDR;
use ring_buffer::*;


pub fn test_nvme_driver() {
    let mut nvme_dev =
        unsafe { NvmeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xfebf_0000, 0x4000)) };

    log::info!("Initializing Nvme driver...");

    nvme_dev.init();

    log::info!("Running Nvme Read/write tests!");

    //run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, true, false, 0);
    //run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, false, false, 0);

    run_blocktest_blkreq(&mut nvme_dev);

    //test_nvme_ring_buffer();
}

/// | MSG_TYPE | PAYLOAD |
/// MSG_TYPE == STOP
///     quit polling

fn test_nvme_ring_buffer() {
    loop {

        // TODO:
        // 1) Fill the queue with new BlockReq's
        //      - Populate BlockReqs
        // 2) Push the BlockReqs into the RingBuffer
        // 3) Poll for BlockResps from the RingBuffer
        // 4) Reclaim BlockReq from BlockResp
        //      - Modify BlockReq's Op (read/write) and the block num
    }
}

fn nvme_driver_backend() {
    loop {
    }
}

#[no_mangle]
pub fn test_nvme_with_ring_buffer_ap()-> ! {
    log::info!("hello from test_nvme_with_ring_buffer_ap");

    unsafe{
        let size = core::mem::size_of::<GenericRingBuffer<BlockReq,BlockResp>>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   
    }

    test_nvme_ring_buffer();

    loop {
        unsafe{asm!("nop");}
    }
}


pub fn test_nvme_with_ring_buffer(){
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
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_nvme_with_ring_buffer_ap as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        // log::info!("request_queue address: {:p}", &request_queue);   

        let size = core::mem::size_of::<GenericRingBuffer<BlockReq,BlockResp>>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut GenericRingBuffer<BlockReq,BlockResp> = &mut*(DATA_BUFFER_ADDR as *mut GenericRingBuffer<BlockReq,BlockResp>);
        buff_ref.init();
        log::info!("data_buffer init done");

        loop{
            let error_code = asys::sys_send_pages_no_wait(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
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
        nvme_driver_backend();
    }
}

