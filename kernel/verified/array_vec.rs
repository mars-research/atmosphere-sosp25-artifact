use core::mem::MaybeUninit;

use vstd::prelude::*;

verus! {

/// A preallocated vector.
pub struct ArrayVec<T, const N: usize> {
    data: MaybeUninitArray<T, N>,
    len: usize,
}

impl<T, const N: usize> ArrayVec<T, N> {
    pub spec fn view(self) -> Seq<T>;

    #[verifier(external_body)]
    pub fn new() -> (vec: Self)
        ensures
            vec@ == Seq::<T>::empty(),
            vec.wf(),
    {
        Self {
            data: MaybeUninitArray::new(),
            len: 0,
        }
    }

    #[verifier(external_body)]
    pub fn index(&self, index: usize) -> (ret: &T)
        requires
            self.wf(),
            index < self.len(),
        ensures
            ret == self@[index as int],
    {
        unsafe {
            self.data.borrow(index)
        }
    }

    #[verifier(external_body)]
    pub fn set(&mut self, index: usize, value: T) -> (ret: &T)
        requires
            old(self).wf(),
            index < old(self).len(),
        ensures
            self@ == old(self)@.update(index as int, value),
            ret == value,
    {
        unsafe {
            self.data.set(index, value)
        }
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: T) -> (ret: &T)
        requires
            old(self).wf(),
            old(self).len() < N,
        ensures
            self@ == old(self)@.push(value),
            ret == value,
    {
        let ret = unsafe {
            self.data.set(self.len, value)
        };

        self.len += 1; // TODO: this operation is invisible to the verifier

        ret
    }

    #[must_use]
    pub fn try_push(&mut self, value: T) -> (ret: Option<&T>)
        requires
            old(self).wf(),
        ensures
            self.wf(),

            // The push succeeds iff there is space
            ret.is_Some() == (old(self).len() < N),
            ret.is_Some() ==> (
                self@ == old(self)@.push(value)
                && ret.get_Some_0() == value
            ),

            // Otherwise, the seq is unchanged
            ret.is_None() ==> self@ == old(self)@,
    {
        if self.len() < N {
            Some(self.push(value))
        } else {
            None
        }
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
        ensures
            ret == old(self)@[old(self).len() - 1],
            self@ == old(self)@.subrange(0, old(self).len() - 1),

            // This doesn't seem to work to re-establish len
            //self@ == old(self)@.drop_last(),
    {
        let ret = unsafe {
            self.data.copy(self.len)
        };

        self.len -= 1; // TODO: this operation is invisible to the verifier

        ret
    }

    pub fn try_pop(&mut self) -> (ret: Option<T>)
        requires
            old(self).wf(),
        ensures
            self.wf(),

            // The pop succeeds iff there is any element
            ret.is_Some() == (old(self).len() > 0),
            ret.is_Some() ==> (
                ret.get_Some_0() == old(self)@[old(self).len() - 1]
                && self@ == old(self)@.subrange(0, old(self).len() - 1)
            ),

            // Otherwise, the seq is unchanged
            ret.is_None() ==> self@ == old(self)@,
    {
        if self.len() > 0 {
            Some(self.pop())
        } else {
            None
        }
    }

    #[verifier(external_body)] // TODO: Verify consistency between exec len and seq len
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_len(),
            ret == self@.len(),
    {
        self.len
    }

    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    pub open spec fn wf(&self) -> bool {
        self.len() <= N
    }
}

/// An unsafe wrapper of `[MaybeUninit<T>; N]`.
///
/// Sadly we can't directly make an external_type_specification because
/// it's a union and not a struct or enum.
#[repr(transparent)]
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(T)]
struct MaybeUninitArray<T, const N: usize>([MaybeUninit<T>; N]);

impl<T, const N: usize> MaybeUninitArray<T, N> {
    #[verifier(external_body)]
    fn new() -> Self {
        Self([(); N].map(|_| {
            MaybeUninit::<T>::uninit()
        }))
    }
}

impl<T, const N: usize> MaybeUninitArray<T, N> {
    #[verifier(external)]
    unsafe fn borrow(&self, index: usize) -> &T {
        self.0[index].assume_init_ref()
    }

    #[verifier(external)]
    unsafe fn copy(&self, index: usize) -> T {
        self.0[index].assume_init_read()
    }

    #[verifier(external)]
    unsafe fn set(&mut self, index: usize, value: T) -> &T {
        let element = self.0[index].assume_init_mut();
        *element = value;
        element
    }
}

mod spec_tests {
    use super::*;

    fn test() {
        let mut vec = ArrayVec::<usize, 5>::new();
        vec.push(1);
        vec.push(2);
        vec.push(3);
        vec.push(4);
        vec.push(5);
        //vec.push(6);
    }

    fn test2() {
        let mut vec = ArrayVec::<usize, 5>::new();
        assert(vec.len() == 0);
        assert(vec.wf());

        vec.push(1);
        assert(vec.len() == 1);
        assert(vec.wf());

        vec.push(2);
        assert(vec.len() == 2);
        assert(vec.wf());

        let x = vec.pop();
        assert(x == 2);
        assert(vec.wf()); // 1 remaining

        let x = vec.try_pop();
        assert(x == Some(1usize));
        assert(vec.wf()); // None remaining

        let x = vec.try_pop();
        assert(x == None::<usize>);
        assert(vec.wf()); // Still wrll-formed
    }
}

}
