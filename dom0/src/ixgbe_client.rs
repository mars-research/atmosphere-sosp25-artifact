use crate::USERSPACE_BASE;
use ixgbe_driver::device::IxgbeDevice;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use pcid::utils::PciBarAddr;

pub fn test_ixgbe_driver() {
    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xfe00_0000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();

    ixgbe_driver::ixgbe_test::run_tx_udptest(&mut ixgbe_dev, 64, false);
}
