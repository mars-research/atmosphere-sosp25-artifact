#![no_std]

const NVME_BAR_PCI_HW: u64 = 0x94c0_0000;
const NVME_BAR_PCI_PT: u64 = 0xfebe_4000;

pub const NVME_BAR_BASE: u64 = NVME_BAR_PCI_PT;
pub const NVME_BAR_SIZE: usize = 0x4000;

// on qemu pci pt, nvme sits on 00:03.0
const NVME_PCI_DEV_PT: (usize, usize, usize) = (0x0, 0x3, 0x0);
// on real hardware (d430) nvme sits on 05:00.0
const NVME_PCI_DEV_HW: (usize, usize, usize) = (0x5, 0x0, 0x0);

pub const NVME_PCI_DEV: (usize, usize, usize) = NVME_PCI_DEV_PT;

pub const DATA_BUFFER_ADDR: u64 = 0xF0_0000_0000;
pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

pub const IOMMU_TEST_ADDR: u64 = 0xF0_0000_0000;

const COM1: usize = 0x3f8;
// d430 baremetal needs COM2
const COM2: usize = 0x2f8;

pub const SPORT_ADDR: usize = COM1;
