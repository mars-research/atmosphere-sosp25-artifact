#[macro_use]
use libdma::Dma;
//use crate::println;
use crate::BlockReq;
use crate::NUM_LBAS;
use core::arch::asm;
use libdma::nvme::allocate_dma;
use libdma::nvme::{NvmeCommand, NvmeCompletion};
use libdma::DmaAllocator;

#[repr(align(4096))]
pub(crate) struct NvmeCommandQueue {
    pub data: Dma<[NvmeCommand; QUEUE_DEPTH]>,
    //rand: Rand,
    pub i: usize,
    pub raw_requests: [Option<u64>; QUEUE_DEPTH],
    pub breq_requests: [Option<BlockReq>; QUEUE_DEPTH],
    pub req_slot: [bool; QUEUE_DEPTH],
    block: u64,
}

impl NvmeCommandQueue {
    pub fn new() -> Result<NvmeCommandQueue, i32> {
        let module = Self {
            data: allocate_dma()?,
            i: 0,
            raw_requests: array_init::array_init(|_| None),
            breq_requests: array_init::array_init(|_| None),
            req_slot: [false; QUEUE_DEPTH],
            block: 0,
            //rand: Rand::new(),
        };
        Ok(module)
    }

    pub fn submit(&mut self, entry: NvmeCommand) -> usize {
        self.data[self.i] = entry;
        self.data[self.i].cid = self.i as u16;
        self.i = (self.i + 1) % self.data.len();
        self.i
    }

    pub fn is_submittable(&self) -> bool {
        !self.req_slot[self.i]
    }

    pub fn submit_request_breq(&mut self, entry: NvmeCommand, breq: BlockReq) -> Option<usize> {
        let cur_idx = self.i;
        if self.req_slot[cur_idx] == false {
            self.data[cur_idx] = entry;
            self.data[cur_idx].cid = cur_idx as u16;
            self.data[cur_idx].cdw10 %= NUM_LBAS as u32;
            let cid = cur_idx as u16;

            //println!("Submitting block[{}] {} at slot {}", cid, breq.block, cur_idx);

            self.breq_requests[cur_idx] = Some(breq);

            self.req_slot[cur_idx] = true;
            self.i = (cur_idx + 1) % self.data.len();
            Some(self.i)
        } else {
            //println!("No free slot");
            None
        }
    }

    pub fn submit_request_raw(&mut self, entry: NvmeCommand, data: u64) -> Option<usize> {
        let cur_idx = self.i;
        if self.req_slot[cur_idx] == false {
            self.data[cur_idx] = entry;
            self.data[cur_idx].cid = cur_idx as u16;
            let cid = cur_idx as u16;

            self.raw_requests[cur_idx] = Some(data);
            self.data[cur_idx].cdw10 = self.block as u32;

            self.block = (self.block + 8) % NUM_LBAS;

            log::trace!(
                "Submitting block[{}] {} at slot {}",
                cid,
                self.block,
                cur_idx
            );

            self.req_slot[cur_idx] = true;
            self.i = (cur_idx + 1) % self.data.len();
            Some(self.i)
        } else {
            //println!("No free slot");
            None
        }
    }
}

pub const QUEUE_DEPTH: usize = 256;

pub(crate) struct NvmeCompletionQueue {
    pub data: Dma<[NvmeCompletion; QUEUE_DEPTH]>,
    pub i: usize,
    pub phase: bool,
}

impl NvmeCompletionQueue {
    pub fn new() -> Result<Self, i32> {
        Ok(Self {
            data: allocate_dma()?,
            i: 0,
            phase: true,
        })
    }

    pub fn get_cq_head(&self) -> usize {
        self.i
    }

    pub(crate) fn complete(&mut self) -> Option<(usize, NvmeCompletion, usize)> {
        let entry = unsafe { core::ptr::read_volatile(self.data.as_ptr().add(self.i)) };
        let mut cq_entry: usize = 0;
        if ((entry.status & 1) == 1) == self.phase {
            cq_entry = self.i;
            self.i = (self.i + 1) % self.data.len();
            if self.i == 0 {
                self.phase = !self.phase;
            }
            //println!("=> {:?}", entry);
            Some((self.i, entry, cq_entry))
        } else {
            None
        }
    }

    pub fn is_valid(&self) -> Option<NvmeCompletion> {
        let entry = unsafe { core::ptr::read_volatile(self.data.as_ptr().add(self.i)) };

        if ((entry.status & 1) == 1) == self.phase {
            //println!("idx {} status {} phase {}", self.i, entry.status, self.phase);
            Some(entry)
        } else {
            //println!("None: idx {} status {} phase {}", self.i, entry.status, self.phase);
            None
        }
    }

    pub fn advance(&mut self) {
        self.i = (self.i + 1) % self.data.len();
        if self.i == 0 {
            //println!("switching phase from {} to {}", self.phase, !self.phase);
            self.phase = !self.phase;
        }
    }

    pub fn complete_spin(&mut self) -> (usize, NvmeCompletion, usize) {
        loop {
            if let Some(some) = self.complete() {
                return some;
            } else {
                unsafe {
                    asm!("pause");
                }
            }
        }
    }
}
