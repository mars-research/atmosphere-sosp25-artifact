#![no_std]

pub(crate) const NUM_LBAS: u64 = 2197504;

extern crate alloc;

use alloc::vec::Vec;

pub mod cmd;
pub mod device;
pub mod nvme_test;
mod queue;
mod regs;
pub use log::info as println;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum BlockOp {
    Read,
    Write,
}

#[derive(Debug, Clone, Copy)]
pub struct BlockReq {
    pub block: u64,
    pub num_blocks: u16,
    pub data: usize,
    pub op: BlockOp,
}

#[derive(Debug, Clone, Copy)]
pub struct BlockResp {
    pub req: BlockReq,
    pub res: i32,
}

impl BlockReq {
    pub fn new(block: u64, num_blocks: u16, data: usize, op: BlockOp) -> BlockReq {
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
