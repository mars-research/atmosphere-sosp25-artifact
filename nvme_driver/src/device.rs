use crate::cmd as nvme_cmd;
use crate::println;
use crate::queue::NvmeCommandQueue;
use crate::queue::NvmeCompletionQueue;
use crate::regs::NvmeArrayRegs;
use crate::regs::{NvmeRegs32, NvmeRegs64};
use crate::NUM_LBAS;
use crate::{BlockOp, BlockReq};
use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::format;
use alloc::vec::Vec;
use asys::sys_mresolve;
use core::{fmt, mem, ptr};
use heapless::String;
use libdma::nvme::{allocate_dma, NvmeCommand, NvmeCompletion};
use libdma::Dma;
use libtime::sys_ns_loopsleep;
use pcid::utils::PciBarAddr;

use ring_buffer::*;

const ONE_MS_IN_NS: u64 = 1000_000;
const NVME_CC_ENABLE: u32 = 0x1;
const NVME_CSTS_RDY: u32 = 0x1;

struct NvmeNamespace {
    pub id: u32,
    pub blocks: u64,
    pub block_size: u64,
}

pub struct NvmeStats {
    completed: u64,
    submitted: u64,
}

impl NvmeStats {
    pub fn get_stats(&self) -> (u64, u64) {
        (self.submitted, self.completed)
    }
    pub fn reset_stats(&mut self) {
        self.submitted = 0;
        self.completed = 0;
    }
}

impl fmt::Display for NvmeStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "submitted {} completed {}",
            self.submitted, self.completed
        )
    }
}

pub struct NvmeDevice {
    submission_queues: [NvmeCommandQueue; 2],
    completion_queues: [NvmeCompletionQueue; 2],
    bar: PciBarAddr,
    namespaces: Vec<NvmeNamespace>,
    dstrd: u16,
    pub stats: NvmeStats,
    //rrequests: [Option<Vec<u8>>; QUEUE_DEPTH],
}

fn wrap_ring(index: usize, ring_size: usize) -> usize {
    (index + 1) & (ring_size - 1)
}

impl NvmeDevice {
    /// Resets and initializes an Nvme device.
    pub fn init(&mut self) {
        println!("Capabilities 0x{:X}", self.read_reg64(NvmeRegs64::CAP));
        println!("Version 0x{:X}", self.read_reg32(NvmeRegs32::VS));
        println!(
            "Controller Configuration 0x{:X}",
            self.read_reg32(NvmeRegs32::CC)
        );
        println!("Contoller Status 0x{:X}", self.read_reg32(NvmeRegs32::CSTS));

        /// 7.6.1 Initialization (Nvme spec 1.4-2019.06.10)
        // Reset the controller
        //self.write_reg32(NvmeRegs32::NSSR, 0x4E564D65);
        self.reset_controller();

        // Configure admin queue
        self.configure_admin_queue();

        // Set entry sizes
        self.set_entry_sizes();

        // set enable bit
        self.write_flag32(NvmeRegs32::CC, 1);

        println!("Waiting for controller to become ready");
        // Wait for controller to become ready
        self.wait_set_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY, 7500);
        println!("Controller is ready!");

        self.identify_controller();

        self.identify_ns_list();

        self.identify_ns(1);

        self.create_io_queues();

        log::info!("Nvme Initialized!");
    }

    pub fn new(bar: PciBarAddr) -> NvmeDevice {
        NvmeDevice {
            bar,
            submission_queues: [
                NvmeCommandQueue::new().unwrap(),
                NvmeCommandQueue::new().unwrap(),
            ],
            completion_queues: [
                NvmeCompletionQueue::new().unwrap(),
                NvmeCompletionQueue::new().unwrap(),
            ],
            namespaces: Vec::new(),
            dstrd: {
                unsafe {
                    ((ptr::read_volatile((bar.get_base() + NvmeRegs64::CAP as u64) as *const u64)
                        >> 32)
                        & 0b1111) as u16
                }
            },
            stats: NvmeStats {
                submitted: 0,
                completed: 0,
            },
        }
    }

    #[inline(always)]
    pub fn read_reg32(&self, reg: NvmeRegs32) -> u32 {
        unsafe { ptr::read_volatile((self.bar.get_base() + reg as u64) as *const u32) }
    }

    fn wait_set_reg32(&self, reg: NvmeRegs32, value: u32, delay_in_ms: u64) {
        loop {
            let current = self.read_reg32(reg);
            if (current & value) == 1 {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * delay_in_ms);
        }
    }

    fn wait_clear_reg32(&self, reg: NvmeRegs32, value: u32) {
        loop {
            let current = self.read_reg32(reg);
            if (current & value) == 0 {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
        }
    }

    fn write_flag32(&self, register: NvmeRegs32, flags: u32) {
        self.write_reg32(register, self.read_reg32(register) | flags);
    }

    fn clear_flag32(&self, reg: NvmeRegs32, flags: u32) {
        self.write_reg32(reg, self.read_reg32(reg) & !flags);
    }

    #[inline(always)]
    pub fn read_reg64(&self, reg: NvmeRegs64) -> u64 {
        unsafe { ptr::read_volatile((self.bar.get_base() + reg as u64) as *const u64) }
    }

    #[inline(always)]
    pub fn write_reg32(&self, reg: NvmeRegs32, val: u32) {
        unsafe {
            ptr::write_volatile((self.bar.get_base() + reg as u64) as *mut u32, val as u32);
        }
    }

    #[inline(always)]
    pub fn write_reg64(&self, reg: NvmeRegs64, val: u64) {
        unsafe {
            ptr::write_volatile((self.bar.get_base() + reg as u64) as *mut u64, val as u64);
        }
    }

    fn set_entry_sizes(&self) {
        self.write_reg32(
            NvmeRegs32::CC,
            self.read_reg32(NvmeRegs32::CC) |
                                (4 << 20) // Sizeof(NvmeCompletion) in power of two
                                | (6 << 16), // Sizeof(NvmeCommand) in power of two
        );
        println!("finish set_entry_sizes");
    }

    fn read_reg_idx(&self, reg: NvmeArrayRegs, qid: u16) -> u32 {
        match reg {
            NvmeArrayRegs::SQyTDBL => unsafe {
                ptr::read_volatile(
                    (self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid)) as u64)
                        as *mut u32,
                )
            },

            NvmeArrayRegs::CQyHDBL => unsafe {
                ptr::read_volatile(
                    (self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid + 1)) as u64)
                        as *mut u32,
                )
            },
        }
    }

    fn write_reg_idx(&self, reg: NvmeArrayRegs, qid: u16, val: u32) {
        match reg {
            NvmeArrayRegs::SQyTDBL => unsafe {
                ptr::write_volatile(
                    (self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid)) as u64)
                        as *mut u32,
                    val,
                );
            },

            NvmeArrayRegs::CQyHDBL => unsafe {
                ptr::write_volatile(
                    (self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid + 1)) as u64)
                        as *mut u32,
                    val,
                );
            },
        }
    }

    pub fn create_io_queues(&mut self) {
        for io_qid in 1..self.completion_queues.len() {
            let (ptr, len) = {
                let queue = &self.completion_queues[io_qid];
                (queue.data.physical(), queue.queue_len)
            };

            println!(
                "  - Attempting to create I/O completion queue {} with virt 0x{:08x} phys 0x{:08x} | len {}",
                io_qid, &*self.completion_queues[io_qid].data as *const _ as u64, ptr, len * core::mem::size_of::<NvmeCompletion>(),
            );
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                let entry =
                    nvme_cmd::create_io_completion_queue(cid, io_qid as u16, ptr, (len - 1) as u16);
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            // println!("  - Waiting to create I/O completion queue {}", io_qid);
            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }
        }

        for io_qid in 1..self.submission_queues.len() {
            let (ptr, len) = {
                let queue = &self.submission_queues[io_qid];
                (queue.data.physical(), queue.data.len())
            };

            println!(
                "  - Attempting to create I/O submission queue {} with virt 0x{:08x} phys 0x{:08x} | len {} | entry_size {} | Q Depth {}",
                io_qid, &*self.submission_queues[io_qid].data as *const _ as u64, ptr, len, core::mem::size_of::<NvmeCommand>(), crate::queue::QUEUE_DEPTH
            );
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                //TODO: Get completion queue ID through smarter mechanism
                let entry = nvme_cmd::create_io_submission_queue(
                    cid,
                    io_qid as u16,
                    ptr,
                    (len - 1) as u16,
                    io_qid as u16,
                );
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            // println!("  - Waiting to create I/O submission queue {}", io_qid);
            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }
        }
    }

    fn submission_queue_tail(&mut self, qid: u16, tail: u16) {
        self.write_reg_idx(NvmeArrayRegs::SQyTDBL, qid, tail as u32);
    }

    fn completion_queue_head(&mut self, qid: u16, head: u16) {
        self.write_reg_idx(NvmeArrayRegs::CQyHDBL, qid, head as u32);
    }

    fn reset_controller(&self) {
        println!("Resetting...");
        self.clear_flag32(NvmeRegs32::CC, NVME_CC_ENABLE);

        println!("Waiting for reset to be acked");
        self.wait_clear_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY);
    }

    pub fn configure_admin_queue(&self) {
        let acq = &self.completion_queues[0];
        let asq = &self.submission_queues[0];

        self.write_reg32(
            NvmeRegs32::AQA,
            ((acq.queue_len as u32 - 1) << 16) | (asq.data.len() as u32 - 1),
        );
        println!(
            "asq.data.virt {:08x} phys {:08x} size {}",
            &*asq.data as *const _ as *const u64 as u64,
            asq.data.physical() as u64,
            asq.data.len(),
        );
        println!(
            "acq.data.virt {:08x} phys {:08x} size {}",
            &*acq.data as *const _ as *const u64 as u64,
            acq.data.physical() as u64,
            acq.queue_len,
        );

        self.write_reg64(NvmeRegs64::ASQ, asq.data.physical() as u64);
        self.write_reg64(NvmeRegs64::ACQ, acq.data.physical() as u64);
        println!("finish configure_admin_queue");
    }

    pub fn identify_controller(&mut self) {
        println!("allocating dma!");
        let data: Dma<[u8; 4096]> = allocate_dma().unwrap();

        // HACK
        println!("reloading iommu");
        unsafe {
            let pml4 = asys::sys_rd_io_cr3() as u64;
            asys::sys_set_device_iommu(0x0, 0x3, 0x0, pml4);
        }

        println!(
            "  - Attempting to identify controller with data {:x}",
            data.physical()
        );
        {
            let qid = 0;
            let queue = &mut self.submission_queues[qid];
            let cid = queue.i as u16;
            let entry = nvme_cmd::identify_controller(cid, data.physical());
            let tail = queue.submit(entry);
            self.submission_queue_tail(qid as u16, tail as u16);
        }

        println!("  - Waiting to identify controller");
        {
            let qid = 0;
            let queue = &mut self.completion_queues[qid];
            let (head, entry, _) = queue.complete_spin();
            self.completion_queue_head(qid as u16, head as u16);
        }

        println!("  - Dumping identify controller");

        let mut serial: String<64> = String::new();
        for &b in &data[4..24] {
            if b == 0 {
                break;
            }
            serial.push(b as char);
        }

        let mut model: String<64> = String::new();
        for &b in &data[24..64] {
            if b == 0 {
                break;
            }
            model.push(b as char);
        }

        let mut firmware: String<8> = String::new();
        for &b in &data[64..72] {
            if b == 0 {
                break;
            }
            firmware.push(b as char);
        }

        println!(
            "  - Model: {} Serial: {} Firmware: {}",
            model.trim(),
            serial.trim(),
            firmware.trim()
        );
    }

    pub fn identify_ns_list(&mut self) {
        let mut nsids = Vec::new();
        {
            //TODO: Use buffer
            let data: Dma<[u32; 1024]> = allocate_dma().unwrap();

            println!("  - Attempting to retrieve namespace ID list");
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                let entry = nvme_cmd::identify_namespace_list(cid, data.physical(), 1);
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            println!("  - Waiting to retrieve namespace ID list");
            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }

            println!("  - Dumping namespace ID list");
            for &nsid in data.iter() {
                if nsid != 0 {
                    nsids.push(nsid);
                }
            }
        }
        println!("nsids len {}", nsids.len());
        for nsid in nsids {
            println!("nsid: {:x}", nsid);
        }
    }

    pub fn identify_ns(&mut self, nsid: u32) {
        let data: Dma<[u8; 4096]> = allocate_dma().unwrap();

        println!("  - Attempting to identify namespace {}", nsid);
        {
            let qid = 0;
            let queue = &mut self.submission_queues[qid];
            let cid = queue.i as u16;
            let entry = nvme_cmd::identify_namespace(cid, data.physical(), nsid);
            let tail = queue.submit(entry);
            self.submission_queue_tail(qid as u16, tail as u16);
        }

        // println!("  - Waiting to identify namespace {}", nsid);
        {
            let qid = 0;
            let queue = &mut self.completion_queues[qid];
            let (head, entry, _) = queue.complete_spin();
            self.completion_queue_head(qid as u16, head as u16);
        }

        // println!("  - Dumping identify namespace");

        unsafe {
            let size = *(data.as_ptr().offset(0) as *const u64);
            let capacity = *(data.as_ptr().offset(8) as *const u64);
            println!(
                "    - ID: {} Size: {} Capacity: {}",
                nsid,
                size * 512,
                capacity * 512,
            );

            //TODO: Read block size
            self.namespaces.push(NvmeNamespace {
                id: nsid,
                blocks: size,
                block_size: 512, // TODO
            });
        }
    }

    pub fn dump_queues(&mut self, qid: usize) {
        println!("| idx | sq | ");
        for i in 0..crate::queue::QUEUE_DEPTH {
            println!("[{}] sq.slot: {} sq.breq_rrefs {}", i, self.submission_queues[qid].req_slot[i],
                                        self.submission_queues[qid].raw_requests_vec[i].is_some());
        }
    }


    pub fn submit_and_poll_breq(
        &mut self,
        submit: &mut VecDeque<BlockReq>,
        collect: &mut VecDeque<BlockReq>,
    ) -> usize {
        let mut sub_count = 0;
        let mut reap_count = 0;
        let mut cur_tail = 0;
        let mut cur_head = 0;
        let batch_sz = 8;
        let reap_all = false;
        let qid = 1;

        while let Some(breq) = submit.pop_front() {
            let buf_addr = breq.data as usize;
            let (ptr0, ptr1) = unsafe { (sys_mresolve(buf_addr).0 as u64, 0) };
            let queue = &mut self.submission_queues[qid];
            //println!("breq 0x{:08x} ptr0 0x{:08x}", buf_addr, ptr0);

            let num_blocks = breq.num_blocks;
            let mut entry;

            if breq.op == BlockOp::Write {
                entry = nvme_cmd::io_write(
                    qid as u16,
                    1,          // nsid
                    breq.block, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            } else {
                entry = nvme_cmd::io_read(
                    qid as u16,
                    1,          // nsid
                    breq.block, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            }

            if queue.is_submittable() {
                if let Some(tail) = queue.submit_request_breq(entry, breq) {
                    cur_tail = tail;
                    sub_count += 1;

                    let queue = &mut self.completion_queues[qid];
                    if let Some((head, entry, cq_idx)) = if reap_all {
                        Some(queue.complete_spin())
                    } else {
                        queue.complete()
                    } {
                        log::trace!("1 Got head {} cq_idx {}", head, cq_idx);
                        let sq = &mut self.submission_queues[qid];
                        if sq.req_slot[cq_idx] == true {
                            if let Some(req) = sq.breq_requests[cq_idx].take() {
                                collect.push_front(req);
                            }
                            sq.req_slot[cq_idx] = false;
                            reap_count += 1;
                        }
                        cur_head = head;
                        //TODO: Handle errors
                        self.stats.completed += 1;
                    }

                    self.stats.submitted += 1;
                }
            } else {
                submit.push_front(breq);
                break;
            }
        }

        if sub_count > 0 {
            self.submission_queue_tail(qid as u16, cur_tail as u16);
        }

        {
            for i in 0..batch_sz {
                let queue = &mut self.completion_queues[qid];
                if collect.len() == 128 {
                    break;
                }
                if let Some((head, entry, cq_idx)) = if reap_all {
                    Some(queue.complete_spin())
                } else {
                    queue.complete()
                } {
                    log::trace!("Got head {} cq_idx {}", head, cq_idx);
                    let sq = &mut self.submission_queues[qid];
                    if sq.req_slot[cq_idx] == true {
                        if let Some(req) = sq.breq_requests[cq_idx].take() {
                            collect.push_front(req);
                        }
                        sq.req_slot[cq_idx] = false;
                        sq.breq_requests[cq_idx] = None;
                        reap_count += 1;
                    } else {
                        println!(
                            "Anomaly: req_slot[{}] blkreq_rrefs[{}] can't collect",
                            cq_idx, cq_idx
                        );
                    }
                    cur_head = head;
                    //TODO: Handle errors
                    self.stats.completed += 1;
                } else {
                    break;
                }
            }
            if reap_count > 0 {
                //println!("updating cur_head {}", cur_head);
                self.completion_queue_head(qid as u16, cur_head as u16);
            }
        }
        sub_count
    }

    pub fn submit_and_poll_raw(
        &mut self,
        submit: &mut VecDeque<Vec<u8>>,
        collect: &mut VecDeque<Vec<u8>>,
        write: bool,
        is_random: bool,
    ) -> usize {
        let mut sub_count = 0;
        let mut reap_count = 0;
        let mut cur_tail = 0;
        let mut cur_head = 0;
        let batch_sz = 32;
        let reap_all = false;
        let qid = 1;

        while let Some(breq) = submit.pop_front() {
            // FIXME: store both (vaddr, paddr) to avoid calling this everytime
            let (ptr0, ptr1) = unsafe { (sys_mresolve(breq.as_ptr() as usize).0 as u64, 0) };
            //println!("breq 0x{:08x} ptr0 0x{:08x}", breq.as_ptr() as u64, ptr0);
            let queue = &mut self.submission_queues[qid];

            let num_blocks = 8;
            let mut entry;

            if write {
                entry = nvme_cmd::io_write(
                    qid as u16,
                    1, // nsid
                    0, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            } else {
                entry = nvme_cmd::io_read(
                    qid as u16,
                    1, // nsid
                    0, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            }

            if queue.is_submittable() {
                if let Some(tail) = if is_random {
                    //queue.submit_request_rand_raw(entry, breq.as_ptr() as u64)
                    queue.submit_request_raw_vec(entry, breq)
                } else {
                    queue.submit_request_raw_vec(entry, breq)
                } {
                    cur_tail = tail;
                    sub_count += 1;

                    /*let queue = &mut self.completion_queues[qid];
                    if let Some((head, entry, cq_idx)) = if reap_all {
                        Some(queue.complete_spin())
                    } else {
                        queue.complete()
                    } {
                        assert_eq!(entry.status >> 1, 0);
                        /*if entry.status >> 1 > 0 {
                            log::info!(
                                "head {} entry {:#?} cq_idx {}  command {:#?}",
                                head,
                                entry,
                                cq_idx,
                                self.submission_queues[qid].data[cq_idx]
                            );
                            sys_ns_loopsleep(100);
                            self.dump_queues(qid);
                            assert_eq!(entry.status >> 1, 0);
                        }*/

                        //println!("Got head {} cq_idx {}", head, cq_idx);
                        let sq = &mut self.submission_queues[qid];
                        if sq.req_slot[cq_idx] == true {
                            if let Some(req) = sq.raw_requests_vec[cq_idx].take() {
                                //let vec =
                                //    unsafe { Vec::from_raw_parts(*req as *mut u8, 4096, 4096) };

                                collect.push_front(req);
                            }
                            sq.req_slot[cq_idx] = false;
                            reap_count += 1;
                        } else {
                            println!("submit_and_poll_raw: Weird! slot finished, but not found!");
                        }
                        cur_head = head;
                        //TODO: Handle errors
                        self.stats.completed += 1;
                    }*/

                    self.stats.submitted += 1;
                }
            } else {
                submit.push_front(breq);
                break;
            }
        }

        if sub_count > 0 {
            self.submission_queue_tail(qid as u16, cur_tail as u16);
            x86::fence::sfence();
            core::hint::black_box(cur_tail);
        }

        {
            for i in 0..batch_sz {
                //if collect.len() == 32 {
                //  break;
                // }
                let queue = &mut self.completion_queues[qid];
                if let Some((head, entry, cq_idx)) = if reap_all {
                    Some(queue.complete_spin())
                } else {
                    queue.complete()
                } {
                    if entry.status >> 1 > 0 {
                        log::info!(
                            "head {} entry {:#?} cq_idx {}  command {:#?}",
                            head,
                            entry,
                            cq_idx,
                            self.submission_queues[qid].data[cq_idx]
                        );
                        //sys_ns_loopsleep(100);
                        assert_eq!(entry.status >> 1, 0);
                    } /*else {
                          log::info!(
                              "==> head {} entry {:#?} cq_idx {} vaddr {:>08x} paddr {:>08x} command {:#?}",
                              head,
                              entry,
                              cq_idx,
                              self.submission_queues[qid].raw_requests[cq_idx].expect("not found"),
                              unsafe {
                                  sys_mresolve(
                                      self.submission_queues[qid].raw_requests[cq_idx]
                                          .expect("not found") as usize,
                                  )
                                  .0
                              },
                              self.submission_queues[qid].data[cq_idx]
                          );
                      }*/
                    //println!("Got head {} cq_idx {}", head, cq_idx);
                    let sq = &mut self.submission_queues[qid];
                    if sq.req_slot[cq_idx] == true {
                        if let Some(req) = sq.raw_requests_vec[cq_idx].take() {
                            //let vec = unsafe { Vec::from_raw_parts(*req as *mut u8, 4096, 4096) };

                            collect.push_front(req);
                        }
                        sq.req_slot[cq_idx] = false;
                        sq.raw_requests_vec[cq_idx] = None;
                        reap_count += 1;
                    }
                    cur_head = head;
                    //TODO: Handle errors
                    self.stats.completed += 1;
                } else {
                    break;
                }
            }
            if reap_count > 0 {
                //x86::fence::sfence();
                self.completion_queue_head(qid as u16, cur_head as u16);
                x86::fence::sfence();
            }
        }

        sub_count
    }

    pub fn poll_breq(&mut self, collect: &mut VecDeque<BlockReq>) -> usize {
        let qid = 1;
        let mut count: usize = 0;
        let mut reap_count = 0;
        let mut cur_head = 0;
        let reap_all = false;

        let cq = &mut self.completion_queues[qid];
        let sq = &mut self.submission_queues[qid];
        /*println!("| idx | sq | ");
        for i in 0..crate::queue::QUEUE_DEPTH {
            println!("[{}] sq.slot: {} sq.breq_rrefs {}", i, sq.req_slot[i],
                     sq.blkreq_rrefs[i].is_some());
        }*/

        loop {
            let cq = &mut self.completion_queues[qid];
            let sq = &mut self.submission_queues[qid];

            let cid = cq.get_cq_head() % cq.data.len();

            if sq.req_slot[cid] {
                //println!("be-> cid {} rref_valid {} cq[].valid {}", cid, sq.blkreq_rrefs[cid].is_some(),
                //                                               cq.is_valid().is_some());
                if let Some((head, entry, cq_idx)) = if reap_all {
                    Some(cq.complete_spin())
                } else {
                    cq.complete()
                } {
                    //println!("af-> Got head {} cid {} cq_idx {} rref_valid {}", head, cid, cq_idx,
                    //                                sq.blkreq_rrefs[cq_idx].is_some());
                    //assert_eq!(cid, cq_idx, "cid {} cq_idx {}", cid, cq_idx);

                    if let Some(mut req) = sq.breq_requests[cq_idx].take() {
                        collect.push_back(req);
                    }
                    sq.req_slot[cq_idx] = false;
                    sq.breq_requests[cq_idx] = None;
                    reap_count += 1;
                    cur_head = head;
                    //TODO: Handle errors
                    self.stats.completed += 1;
                }
            } else {
                break;
            }
            count += 1;

            if count == cq.data.len() {
                break;
            }
        }
        if reap_count > 0 {
            println!("poll_rref: Updating cq_head to {}", cur_head);
            self.completion_queue_head(qid as u16, cur_head as u16);
        }
        reap_count
    }

    pub fn poll_raw(&mut self, collect: &mut VecDeque<Vec<u8>>) -> usize {
        let qid = 1;
        let mut count: usize = 0;
        let mut reap_count = 0;
        let mut cur_head = 0;
        let reap_all = false;

        let cq = &mut self.completion_queues[qid];
        let sq = &mut self.submission_queues[qid];

        loop {
            let cq = &mut self.completion_queues[qid];
            let sq = &mut self.submission_queues[qid];

            let cid = cq.get_cq_head() % cq.queue_len;

            if sq.req_slot[cid] {
                if let Some((head, entry, cq_idx)) = if reap_all {
                    Some(cq.complete_spin())
                } else {
                    cq.complete()
                } {
                    if let Some(req) = sq.raw_requests_vec[cq_idx].take() {
                        //let vec = unsafe { Vec::from_raw_parts(*req as *mut u8, 4096, 4096) };

                        collect.push_front(req);
                    }
                    sq.req_slot[cq_idx] = false;
                    sq.raw_requests_vec[cq_idx] = None;
                    reap_count += 1;
                    cur_head = head;
                    //TODO: Handle errors
                    self.stats.completed += 1;
                }
            } else {
                break;
            }
            count += 1;

            if count == cq.queue_len {
                break;
            }
        }
        if reap_count > 0 {
            println!("poll_rref: Updating cq_head to {}", cur_head);
            self.completion_queue_head(qid as u16, cur_head as u16);
        }
        reap_count
    }

    pub fn submit_and_poll_breq_with_ringbuffer(
        &mut self,
        submit: &mut RingBuffer<GenericRingBufferNode<BlockReq>, SIZE_OF_QUEUE>,
        collect: &mut RingBuffer<GenericRingBufferNode<BlockReq>, SIZE_OF_QUEUE>,
    ) -> usize {
        let mut sub_count = 0;
        let mut reap_count = 0;
        let mut cur_tail = 0;
        let mut cur_head = 0;
        let batch_sz = 32;
        let reap_all = false;
        let qid = 1;

        while let Some(breq) = submit.try_read() {
            let buf_addr = breq.data as usize;
            let (ptr0, ptr1) = unsafe { (sys_mresolve(buf_addr).0 as u64, 0) };
            let queue = &mut self.submission_queues[qid];
            //println!("breq 0x{:08x} ptr0 0x{:08x}", buf_addr, ptr0);

            let num_blocks = breq.num_blocks;
            let mut entry;

            if breq.op == BlockOp::Write {
                entry = nvme_cmd::io_write(
                    qid as u16,
                    1,          // nsid
                    breq.block, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            } else {
                entry = nvme_cmd::io_read(
                    qid as u16,
                    1,          // nsid
                    breq.block, // block to read
                    (num_blocks - 1) as u16,
                    ptr0,
                    ptr1,
                );
            }

            if queue.is_submittable() {
                if let Some(tail) = queue.submit_request_breq(entry, breq) {
                    cur_tail = tail;
                    sub_count += 1;

                    // let queue = &mut self.completion_queues[qid];
                    // if let Some((head, entry, cq_idx)) = if reap_all {
                    //     Some(queue.complete_spin())
                    // } else {
                    //     queue.complete()
                    // } {
                    //     log::trace!("1 Got head {} cq_idx {}", head, cq_idx);
                    //     let sq = &mut self.submission_queues[qid];
                    //     if sq.req_slot[cq_idx] == true {
                    //         if let Some(req) = sq.breq_requests[cq_idx].take() {
                    //             collect.push_front(req);
                    //         }
                    //         sq.req_slot[cq_idx] = false;
                    //         reap_count += 1;
                    //     }
                    //     cur_head = head;
                    //     //TODO: Handle errors
                    //     self.stats.completed += 1;
                    // }

                    self.stats.submitted += 1;
                    submit.try_free();
                }
            } else {
                // submit.push_front(breq);
                break;
            }

            if sub_count >= batch_sz {
                break;
            }
        }

        if sub_count > 0 {
            self.submission_queue_tail(qid as u16, cur_tail as u16);
        }

        {
            loop {
                let queue = &mut self.completion_queues[qid];

                if collect.is_full() || reap_count >= batch_sz {
                    break;
                }

                if let Some((head, entry, cq_idx)) = if reap_all {
                    Some(queue.complete_spin())
                } else {
                    queue.complete()
                } {
                    log::trace!("Got head {} cq_idx {}", head, cq_idx);
                    let sq = &mut self.submission_queues[qid];
                    if sq.req_slot[cq_idx] == true {
                        if let Some(req) = sq.breq_requests[cq_idx].take() {
                            while collect.try_push(&req) == false {}
                        }
                        sq.req_slot[cq_idx] = false;
                        sq.breq_requests[cq_idx] = None;
                        reap_count += 1;
                    } else {
                        println!(
                            "Anomaly: req_slot[{}] blkreq_rrefs[{}] can't collect",
                            cq_idx, cq_idx
                        );
                    }
                    cur_head = head;
                    //TODO: Handle errors
                    self.stats.completed += 1;
                } else {
                    break;
                }
            }
            if reap_count > 0 {
                //println!("updating cur_head {}", cur_head);
                self.completion_queue_head(qid as u16, cur_head as u16);
            }
        }
        sub_count
    }
}
