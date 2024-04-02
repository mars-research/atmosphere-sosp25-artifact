extern crate nvme_driver;

use crate::USERSPACE_BASE;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::{run_blocktest_blkreq, run_blocktest_raw_with_delay};
use pcid::utils::PciBarAddr;
use ring_buffer::{RingBuffer, SIZE_OF_BUFFER, SIZE_OF_QUEUE};

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

#[repr(align(4096))]
#[repr(C)]
pub struct GenericRingBuffer<I, J> {
    pub request_queue: RingBuffer<I, SIZE_OF_QUEUE>,
    pub reply_queue: RingBuffer<J, SIZE_OF_QUEUE>,
    pub free_stack: [usize; SIZE_OF_QUEUE],
    pub data_buffer: [[usize; SIZE_OF_BUFFER]; SIZE_OF_QUEUE],
    pub len: usize,
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

        // TODO:
        // 1) Poll for BlockReqs from the RingBuffer
        // 2) Submit the BlockReqs to submit_and_poll_breq()
        // 3) Collect the BlockReqs and convert it into BlockResps
        // 4) Push the BlockResps into the RingBuffer
    }
}
