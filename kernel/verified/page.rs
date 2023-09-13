use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SIZE,
};

verus! {

pub type PagePPtr = PPtr<[u8; PAGE_SIZE]>;
pub type PagePerm = PointsTo<[u8; PAGE_SIZE]>;

pub type VAddr = u64;
pub type PAddr = u64;

pub type Cr3 = usize;

}
