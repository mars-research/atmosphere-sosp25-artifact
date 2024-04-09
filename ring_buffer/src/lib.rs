#![no_std]

use core::option::*;
use core::option::Option::*;
use nvme_driver::*;
use core::mem::MaybeUninit;
use pcid::utils::PciBarAddr;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::run_blocktest_blkreq;

pub const SIZE_OF_QUEUE:usize = 4096;
pub const SIZE_OF_BUFFER:usize = 4096;

pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

#[repr(align(4096))]
#[repr(C)]
pub struct DataBufferAllocWrapper{
    pub request_queue:RingBuffer::<usize,SIZE_OF_QUEUE>,
    pub reply_queue:RingBuffer::<usize,SIZE_OF_QUEUE>,
    pub free_stack:[usize;SIZE_OF_QUEUE],
    pub data_buffer:[[u8;SIZE_OF_BUFFER];SIZE_OF_QUEUE],
    pub len:usize,
}
impl DataBufferAllocWrapper{
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

#[repr(align(64))]
#[repr(C)]
pub struct RingBuffer<T,const N: usize>{
    pub head: usize,
    pub head_padding: [usize;8],
    pub ar: [T;N],
    pub tail_padding: [usize;8],
    pub tail: usize,
}

impl <const N: usize> RingBuffer<usize, N>{
    pub const fn new()-> Self{
        Self{
            head:0,
            head_padding:[0;8],
            ar:[usize::MAX;N],
            tail_padding:[0;8],
            tail:0,
        }
    }

    pub fn init(&mut self){
        self.head = 0;
        self.tail = 0;
        for i in 0..N{
            self.ar[i] = usize::MAX;
        }
    }

    pub fn try_push(&mut self, target:usize) -> bool{
        if target == usize::MAX{
            return false;
        }
        if self.ar[self.head] != usize::MAX{
            return false;
        }else{
            self.ar[self.head] = target;
            if self.head == N - 1{
                self.head = 0;
            }else{
                self.head = self.head + 1;
            }
            return true;
        }
    }

    pub fn try_pop(&mut self) -> Option<usize>{
        if self.ar[self.tail] == usize::MAX{
            return None;
        }else{
            let ret = Some(self.ar[self.tail]);
            self.ar[self.tail] = usize::MAX;
            if self.tail == N - 1{
                self.tail = 0;
            }else{
                self.tail = self.tail + 1;
            }
            return ret;
        }
    }
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

    pub fn is_full(&self) -> bool{
        if self.ar[self.head].is_free(){
            return false;
        }else{
            return true;
        }
    }

    pub fn is_empty(&self) -> bool{
        if self.ar[self.tail].is_free(){
            return true;
        }else{
            return false;
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

        for i in 0..SIZE_OF_QUEUE{
            self.free_stack[self.len] = &self.data_buffer[i] as *const u8 as usize;
            self.len = self.len + 1;
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

#[derive(Debug, Clone, Copy)]
pub struct IxgbePayLoad{
    pub addr: usize,
    pub len: usize,
}