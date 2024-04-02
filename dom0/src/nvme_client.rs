extern crate nvme_driver;

use crate::USERSPACE_BASE;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::{run_blocktest_blkreq, run_blocktest_raw_with_delay};
use pcid::utils::PciBarAddr;

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
