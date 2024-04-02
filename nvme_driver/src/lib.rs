#![no_std]

pub(crate) const NUM_LBAS: u64 = 781422768;

extern crate alloc;

use alloc::vec::Vec;

pub mod cmd;
pub mod device;
pub mod nvme_test;
mod queue;
mod regs;
pub use log::info as println;

#[derive(PartialEq, Eq)]
pub enum BlockOp {
    Read,
    Write,
}

pub struct BlockReq {
    pub block: u64,
    num_blocks: u16,
    data: Vec<u8>,
    op: BlockOp,
}

struct BlockResp {
    req: BlockReq,
    res: i32,
}

impl BlockReq {
    pub fn new(block: u64, num_blocks: u16, data: Vec<u8>, op: BlockOp) -> BlockReq {
        BlockReq {
            block,
            num_blocks,
            data,
            op,
        }
    }
}

impl BlockResp {
    pub fn new(req: BlockReq, res: i32) -> Self {
        BlockResp { req, res }
    }
}
