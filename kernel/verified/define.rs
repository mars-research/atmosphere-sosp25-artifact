use vstd::prelude::*;
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
}