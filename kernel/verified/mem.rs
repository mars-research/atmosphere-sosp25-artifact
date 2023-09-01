use vstd::prelude::*;

verus! {

// Idea: https://github.com/verus-lang/verus/pull/361
pub spec fn spec_size_of<T>() -> usize;

#[verifier(external_body)]
#[verifier(when_used_as_spec(spec_size_of))]
pub const fn size_of<T>() -> (ret: usize)
    ensures ret == spec_size_of::<T>(),
{
    core::mem::size_of::<T>()
}

}
