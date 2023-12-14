use vstd::prelude::*;
use vstd::ptr::*;
verus! {

pub type ErrorCodeType = usize;
pub const SUCCESS: ErrorCodeType = 0;
pub const SENDER_ENDPOINT_NOT_EXIST: ErrorCodeType = 1;
pub const RECEIVER_ENDPOINT_EXIST: ErrorCodeType = 2;
pub const RECEIVER_ENDPOINT_USED: ErrorCodeType = 3;
pub const SENDER_ENDPOINT_OUT_OF_BOUND: ErrorCodeType = 4;
pub const NO_RECEIVER:ErrorCodeType = 5;
pub const SCHEDULER_NO_SPACE:ErrorCodeType = 6;
pub const SHARED_ENDPOINT_NOT_EXIST:ErrorCodeType = 7;
pub const SHARED_ENDPOINT_REF_COUNT_OVERFLOW:ErrorCodeType = 8;
pub const SHARED_ENDPOINT_SLOT_TAKEN:ErrorCodeType = 9;


pub type ThreadState = usize;
pub const SCHEDULED:usize = 1;
pub const BLOCKED:usize = 2;
pub const RUNNING:usize = 3;
pub const TRANSIT:usize = 4;

pub type EndpointState = bool;
pub const RECEIVE:EndpointState = true;
pub const SEND:EndpointState = false;

pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointIdx = usize;
pub type EndpointPtr = usize;

pub const MAX_NUM_ENDPOINT_DESCRIPTORS:usize = 32;
pub const MAX_NUM_THREADS_PER_PROC:usize = 500;
pub const MAX_NUM_THREADS_PER_ENDPOINT:usize = 500;
pub const MAX_NUM_PROCS:usize = PCID_MAX;
pub const MAX_NUM_THREADS:usize = 500 * 4096;
pub const IPC_MESSAGE_LEN:usize = 1024;
pub const IPC_PAGEPAYLOAD_LEN:usize = 128;

pub const NUM_PAGES:usize = 4*1024*1024; //16GB
pub const PAGE_SIZE:usize = 4096;
pub const MAX_USIZE:u64 = 31*1024*1024*1024;

pub const DOM0_NUM_PAGES:usize = 1024;

pub type PageType = u8;
pub const R:PageType = 1;
pub const RW:PageType = 2;
pub const RX:PageType = 3;
pub const RWX:PageType = 4;

pub type PageState = usize;

pub const UNAVAILABLE:PageState = 0;
pub const FREE:PageState = 1;
pub const PAGETABLE:PageState = 2;
pub const ALLOCATED:PageState = 3;
pub const MAPPED:PageState = 4;

pub type PageTablePtr = usize;
pub const PCID_MAX:usize = 4096;

pub type PagePPtr = PPtr<[u8; PAGE_SIZE]>;
pub type PagePtr = usize;
pub type PagePerm = PointsTo<[u8; PAGE_SIZE]>;

pub type VAddr = u64;
pub type PAddr = u64;

pub type Pcid = usize;
}