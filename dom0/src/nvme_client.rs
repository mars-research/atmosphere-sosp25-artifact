extern crate nvme_driver;
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
#[derive(Debug, Clone, Copy)]
#[repr(align(64))]
pub struct GenericRingBufferNode<T>{
    pub is_free:bool,
    pub value: T,
}

impl <T: Copy + Clone> GenericRingBufferNode<T>{
    pub fn is_free(&self) -> bool{
        return self.is_free;
    }
    pub fn free_value(&mut self){
        self.is_free = true;
    }
    pub fn set_value(&mut self, target: &T){
        self.value = *target;
        self.is_free = false;
    }
} 


#[repr(align(4096))]
#[repr(C)]
pub struct GenericRingBuffer<I, J> {
    pub request_queue: RingBuffer<GenericRingBufferNode<I>, SIZE_OF_QUEUE>,
    pub reply_queue: RingBuffer<GenericRingBufferNode<J>, SIZE_OF_QUEUE>,
    pub free_stack: [usize; SIZE_OF_QUEUE],
    pub data_buffer: [[u8; SIZE_OF_BUFFER]; SIZE_OF_QUEUE],
    pub len: usize,
}

impl <const N: usize, T: Copy + Clone> RingBuffer<GenericRingBufferNode<T>, N>{
    pub const fn new()-> Self{
        unsafe{
            Self{
                head:0,
                head_padding:[0;8],
                ar:MaybeUninit::uninit().assume_init(),
                tail_padding:[0;8],
                tail:0,
            }
        }
    }

    pub fn init(&mut self){
        self.head = 0;
        self.tail = 0;
        for i in 0..N{
            self.ar[i].free_value();
        }
    }

    pub fn try_push(&mut self, target:&T) -> bool{
        if self.ar[self.head].is_free() == false{
            return false;
        }else{
            self.ar[self.head].set_value(target);
            if self.head == N - 1{
                self.head = 0;
            }else{
                self.head = self.head + 1;
            }
            return true;
        }
    }

    pub fn try_pop(&mut self) -> Option<T>{
        if self.ar[self.tail].is_free(){
            return None;
        }else{
            let ret = Some(self.ar[self.tail].value);
            self.ar[self.tail].free_value();
            if self.tail == N - 1{
                self.tail = 0;
            }else{
                self.tail = self.tail + 1;
            }
            return ret;
        }
    }

    pub fn try_read(&self) -> Option<T>{
        if self.ar[self.tail].is_free(){
            return None;
        }else{
            let ret = Some(self.ar[self.tail].value);
            return ret;
        }
    }

    pub fn try_free(&mut self) -> bool {
        if self.ar[self.tail].is_free(){
            return false;
        }else{
            self.ar[self.tail].free_value();
            if self.tail == N - 1{
                self.tail = 0;
            }else{
                self.tail = self.tail + 1;
            }
            return true;
        }
    }
}


impl<I: Copy, J: Copy> GenericRingBuffer<I, J> {
    pub fn init(&mut self){
        self.request_queue.init();
        self.reply_queue.init();
        self.len = 0;
        for i in 0..SIZE_OF_QUEUE{
            for j in 0..SIZE_OF_BUFFER{
                self.data_buffer[i][j] = 0;
            }
        }
    }

    pub fn allocator_len(&self) -> usize{
        self.len
    }

    pub fn try_push_allocator(&mut self, value:usize) -> bool{
        if self.len < SIZE_OF_QUEUE{
            self.free_stack[self.len] = value;
            self.len += 1;
            true
        }else{
            false
        }
    }

    pub fn try_pop_allocator(&mut self) -> Option<usize>{
        if self.len > 0 {
            self.len -= 1;
            Some(self.free_stack[self.len])
        }else{
            None
        }
    }
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

