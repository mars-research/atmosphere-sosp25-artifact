#![no_std]

pub(crate) const NUM_LBAS: u64 = 781422768;

extern crate alloc;

pub mod cmd;
pub mod device;
pub mod nvme_test;
mod queue;
mod regs;
pub use log::info as println;
