use vstd::prelude::*;
use crate::array::Array;

verus! {

/// A preallocated vector.
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T, const N: usize> ArrayVec<T, N> {
    pub fn new() -> (ret: Self)
        requires
            0 <= N <= usize::MAX, // Verus doesn't know
        ensures
            ret.wf(),
            ret.len() == 0,
            ret.capacity() == N,
    {
        let ret = Self {
            data: Array::new(),
            len: 0,
        };

        ret
    }

    pub open spec fn view(&self) -> Seq<T>
        recommends self.wf(),
    {
        self.view_until(self.len() as nat)
    }

    pub open spec fn view_until(&self, len: nat) -> Seq<T>
        recommends
            0 <= len <= self.len() as nat,
        decreases len
    {
        Seq::<T>::new(len, |i: int| self.data.map()[i as nat])
        /*
        if len <= 0 {
            Seq::<T>::empty()
        } else {
            let prev = len - 1;
            self.view_until(prev as nat)
                .push(self.data.map()[prev as nat])
        }
        */
    }

    pub open spec fn unique(&self) -> bool{
        forall|i:int,j:int| #![auto] 0<=i<self.len() && 0<=j<self.len() && i != j ==> ! (self@[i] =~= self@[j])
    }

    pub closed spec fn wf(&self) -> bool {
        &&& 0 <= N <= usize::MAX
        &&& self.len() <= self.capacity()

        // The element is set if and only if the index is in range
        //
        // The `i >= self.len()` case is important because we want all
        // popped elements to be dropped
        &&& forall |i: nat| (0 <= i < self.len()) == self.data.has_index(i)
    }

    
    #[verifier(inline)]
    pub open spec fn spec_index(&self, index: int) -> (ret: &T) {
        &self@[index]
    }

    pub fn index(&self, index: usize) -> (ret: &T)
        requires
            self.wf(),
            index < self.len(),
        ensures
            ret == self@[index as int],
    {
        self.data.borrow(index)
    }

    pub fn push(&mut self, value: T) -> (ret: &T)
        requires
            old(self).wf(),
            old(self).len() < old(self).capacity(),
        ensures
            self.wf(),
            self@ =~= old(self)@.push(value),
            self.len() == old(self).len() + 1,
            ret == value,
    {
        let index = self.len;
        let ret = self.data.insert(index, value);

        self.len = self.len + 1;

        ret
    }
    
    pub fn push_unique(&mut self, value: T) -> (ret: &T)
    requires
        old(self).wf(),
        old(self).len() < old(self).capacity(),
        old(self).unique(),
        old(self)@.contains(value) == false,
    ensures
        self.wf(),
        self@ =~= old(self)@.push(value),
        self.len() == old(self).len() + 1,
        self.unique(),
        forall|t:T| #![auto] !( t =~= value) ==> old(self)@.contains(t) == self@.contains(t),
        self@.contains(value),
    {
        let index = self.len;
        let ret = self.data.insert(index, value);

        self.len = self.len + 1;

        assert(self@ =~= old(self)@.push(value));

        assert(forall|t:T| #![auto] !( t =~= value) ==> self@.contains(t) ==> old(self)@.contains(t));
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self)@.contains(t) ==> self@[old(self)@.index_of(t)] =~= t);
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self)@.contains(t) ==> self@.contains(t));
        assert(forall|i:int| #![auto] 0<=i<old(self).len() ==> ! (self@[i] =~= value));
        assert(self@[self.len - 1] =~= value);
        ret
    }

    pub fn pop(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
        ensures
            self.wf(),
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
    {
        let index = self.len() - 1;
        let ret = self.data.take(index);

        self.len = self.len - 1;

        ret
    }

    pub fn pop_unique(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
            old(self).unique(),
        ensures
            self.wf(),
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
            self.unique(),
            self@.contains(ret) == false,
            forall|t:T| #![auto] !( t =~= ret) ==> old(self)@.contains(t) == self@.contains(t),
    {
        let index = self.len() - 1;
        let ret = self.data.take(index);

        self.len = self.len - 1;

        assert(self@ =~= old(self)@.drop_last());
        assert(self.unique());
        assert(ret == old(self)@[old(self).len() - 1]);
        assert(forall|i:int| #![auto] 0<=i<old(self).len() - 1 ==> !(self@[i] =~= ret)); 

        assert(old(self)@.contains(ret));
        assert(self@.contains(ret) == false);
        assert(forall|t:T| #![auto] !( t =~= ret) ==> self@.contains(t) ==> old(self)@.contains(t));

        
        assert(forall|t:T| #![auto] !( t =~= ret) ==> !self@.contains(t) ==> !old(self)@.drop_last().contains(t));
        assert(old(self)@[old(self)@.len() - 1] == ret);
        assert(forall|t:T| #![auto] !( t =~= ret) ==> !self@.contains(t) ==> !old(self)@.subrange(old(self)@.len() - 1, old(self)@.len() as int).contains(t));
        assert(old(self)@.drop_last() + old(self)@.subrange(old(self)@.len() - 1, old(self)@.len() as int) =~= old(self)@);
        assert(forall|t:T| #![auto] !( t =~= ret) ==> !self@.contains(t) ==> !old(self)@.contains(t));

        assert(forall|t:T| #![auto] !( t =~= ret) ==> old(self)@.contains(t) ==> self@.contains(t));

        ret
    }

    pub fn set(&mut self, index: usize, value: T)
        requires
            old(self).wf(),
            index < old(self).len(),
        ensures
            self.wf(),
            self@ =~= old(self)@.update(index as int, value),
    {
        self.data.take(index); // drops the old one
        self.data.insert(index, value);
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_len(),
    {
        self.len
    }

    pub closed spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        N
    }

    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

    /*
    proof fn prove_view_consistency(&self, len: nat)
        requires
            self.wf(),
            len <= self.len(),

            len > 0 ==> (
                forall |i: nat| 0 <= i < len - 1 ==>
                    #[trigger] self@[i as int] == #[trigger] self.data.map()[i]
            ),
        ensures
            forall |i: nat| 0 <= i < len ==>
                #[trigger] self@[i as int] == #[trigger] self.data.map()[i],
        decreases len
    {
        if len > 0 {
            let prev = len - 1;
            self.prove_view_consistency(prev as nat);
        }
    }

    proof fn prove_view_equivalence(&self, other: &Self, len: nat)
        requires
            len <= self.len(),
            len <= other.len(),

            forall |i: nat| 0 <= i < len ==>
                self.data.map()[i] == other.data.map()[i],
        ensures
            self.view_until(len) =~= other.view_until(len),
        decreases len
    {
        if len > 0 {
            let prev = len - 1;
            self.prove_view_equivalence(other, prev as nat);
        }
    }
    */
}

mod spec_tests {
    use super::*;

    fn test() {
        let mut vec = ArrayVec::<usize, 5>::new();

        assert(vec.len() == 0);
        vec.push(1);
        assert(vec.len() == 1);
        vec.push(2);
        vec.push(3);
        vec.push(4);
        vec.push(5);

        assert(vec.len() == vec.capacity());
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

        let x = vec.pop();
        assert(x == 1);
        assert(vec.wf()); // None remaining
    }
}

}
