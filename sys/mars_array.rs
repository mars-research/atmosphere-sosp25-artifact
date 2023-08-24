// // https://verus-lang.github.io/verus/guide

// #![no_main]
// #![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

// extern crate core;
// extern crate alloc;

// extern crate builtin;
// extern crate builtin_macros;

// #[allow(unused_imports)]
// use builtin_macros::verus;
// #[allow(unused_imports)]
// use builtin::*;
// #[allow(unused_imports)]
// mod pervasive;
// #[allow(unused_imports)]
// use pervasive::*;
// #[allow(unused_imports)]
// use pervasive::seq::*;
// #[allow(unused_imports)]
// use pervasive::vec::*;
// #[allow(unused_imports)]
// use pervasive::map::*;
// #[allow(unused_imports)]
// use pervasive::set::*;
// #[allow(unused_imports)]
// use pervasive::ptr::*;

use super::*;

verus! {

pub struct MarsArray<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> MarsArray<A, N> {

    #[verifier(external_body)]
    pub fn get(&self, i: usize) -> (out: &A) 
        requires 
            0 <= i < N,
            self.seq@.len() == N,
        ensures
            *out == self.seq@.index(i as int),
            self.seq@.len() == N,
    {
        &self.ar[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, out: A) 
        requires 
            0 <= i < N,
            old(self).wf(),
        ensures
            self.seq@ == old(self).seq@.update(i as int, out),
            self.wf(),
    {
        self.ar[i] = out;
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A 
        recommends self.seq@.len() == N,
                   0 <= i < N,
    {
        self.seq@[i]
    }

    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

    pub open spec fn is_unique(&self) -> bool{
        forall|i: int, j:int| #![auto] i != j && 0<= i < N &&  0<= j < N ==> self.seq@[i] != self.seq@[j]
    }

}

    fn test<const N: usize>(ar: &mut MarsArray<u64, N>)
    requires 
        old(ar).wf(),
        old(ar)[1] == 0,
        N == 2,
            
    {
    let v_1 = ar.get(1);
    assert(v_1 == 0);
    ar.set(0,1);
    let v_0 = ar.get(0);
    assert(v_0 == 1);
    let v_1_new = ar.get(1);
    // assert(v_1_new != 0); // this should fail
    }

    // pub fn test1()
    //     requires true == false,
    // {
    //     assert(false);
    // }

}