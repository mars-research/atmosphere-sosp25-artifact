use vstd::prelude::*;
verus! {

pub type ErrorCodeType = usize;
pub const SENDER_ENDPOINT_NOT_EXIST: ErrorCodeType = 1;
pub const RECEIVER_ENDPOINT_EXIST: ErrorCodeType = 2;
pub const RECEIVER_ENDPOINT_USED: ErrorCodeType = 3;
}