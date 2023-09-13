use core::mem::MaybeUninit;

use vstd::prelude::*;

verus! {

/// An array containing values that might not have been initialized.
///
/// See `ArrayVec` that builds on top of this and behaves
/// like a `Vec`.
#[repr(transparent)]
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub struct Array<T, const N: usize>([MaybeUninit<T>; N]);

impl<T, const N: usize> Array<T, N> {
    // Intentionally not view() that returns Seq<T>, which is proven in ArrayVec
    pub spec fn map(&self) -> Map<nat, T>;

    #[verifier(inline)]
    pub open spec fn has_index(&self, index: nat) -> bool {
        self.map().dom().contains(index)
    }

    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.map() == Map::<nat, T>::empty(),
    {
        Self([(); N].map(|_| {
            MaybeUninit::<T>::uninit()
        }))
    }

    #[verifier(external_body)]
    pub fn borrow(&self, index: usize) -> (ret: &T)
        requires
            index < N,
            self.map().dom().contains(index as nat),
        ensures
            ret == self.map()[index as nat],
    {
        unsafe {
            self.0[index].assume_init_ref()
        }
    }

    #[verifier(external_body)]
    pub fn take(&mut self, index: usize) -> (ret: T)
        requires
            index < N,
            old(self).map().dom().contains(index as nat),
        ensures
            self.map() == old(self).map().remove(index as nat),
            ret == old(self).map()[index as nat],
    {
        unsafe {
            self.0[index].assume_init_read()
        }
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, index: usize, value: T) -> (ret: &T)
        requires
            index < N,

            // MaybeUninit::write doesn't drop the previous value, so
            // there must not be one in the first place
            !old(self).map().dom().contains(index as nat),
        ensures
            self.map() == old(self).map().insert(index as nat, value),
            ret == self.map()[index as nat],
    {
        self.0[index].write(value)
    }
}

mod spec_tests {
    use super::*;

    fn test_x(val: usize) {
        let mut arr = Array::<usize, 5>::new();

        arr.insert(0, val);
        assert(arr.map().dom().contains(0));
        assert(!arr.map().dom().contains(1));

        let val = arr.borrow(0);
        assert(val == val);
        assert(arr.map().dom().contains(0));

        let val = arr.take(0);
        assert(val == val);
        assert(!arr.map().dom().contains(0));
    }
}

}
