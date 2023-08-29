use vstd::prelude::*;

verus! {

// There doesn't appear to be a direct way to use core::mem::size_of
// in spec:
//
// Idea 1: https://github.com/verus-lang/verus/pull/351
pub trait SizeOf: Sized {
    spec fn size_of() -> nat;
}


// Idea 2: https://github.com/verus-lang/verus/pull/361
pub spec fn spec_size_of<T>() -> nat;

#[verifier(external_body)]
pub const fn size_of<T>() -> (ret: usize)
    ensures ret == spec_size_of::<T>(),
{
    core::mem::size_of::<T>()
}

}
