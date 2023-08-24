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

pub struct MarsNoderrayNode<const N: usize>{
    pub seq: Ghost<Seq<Node>>,
    pub ar: [Node;N]
}

impl<const N: usize> MarsNoderrayNode<N> {
    

    #[verifier(external_body)]
    pub fn get(&self, i: usize) -> (out: &Node) 
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
    pub fn set_prev(&mut self, index: usize, prev: Index) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            self.wf(),
            forall |i: int|#![auto] 0<= i < N && i != index ==> self.seq@[i] == old(self).seq@[i],
            self.seq@[index as int].next == old(self).seq@[index as int].next,
            self.seq@[index as int].ptr == old(self).seq@[index as int].ptr,
            self.seq@[index as int].prev == prev,
    {
        self.ar[index].prev = prev;
    }

    #[verifier(external_body)]
    pub fn set_next(&mut self, index: usize, next: Index) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            self.wf(),
            forall |i: int|#![auto] 0<= i < N && i != index ==> self.seq@[i] == old(self).seq@[i],
            self.seq@[index as int].prev == old(self).seq@[index as int].prev,
            self.seq@[index as int].ptr == old(self).seq@[index as int].ptr,
            self.seq@[index as int].next == next,
    {
        self.ar[index].next = next;
    }


    #[verifier(external_body)]
    pub fn set_ptr(&mut self, index: usize, ptr: Pointer) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            self.wf(),
            forall |i: int|#![auto] 0<= i < N && i != index ==> self.seq@[i] == old(self).seq@[i],
            self.seq@[index as int].next == old(self).seq@[index as int].next,
            self.seq@[index as int].prev == old(self).seq@[index as int].prev,
            self.seq@[index as int].ptr == ptr,
    {
        self.ar[index].ptr = ptr;
    }


    // #[verifier(external_body)]
    // pub fn set_prev(&mut self) 
    //     requires 
    //         old(self).wf(),
    //     ensures
    //         self.wf(),
    //         forall |i: int|#![auto] 0<= i < N && i != index ==> self.seq@[i] == old(self).seq@[i],
    //         self.seq@[index as int].next == old(self).seq@[index as int].next,
    //         self.seq@[index as int].ptr == old(self).seq@[index as int].ptr,
    //         self.seq@[index as int].prev == prev,
    // {
    //     self.ar[index].prev = prev;
    // }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> Node 
        recommends self.seq@.len() == N,
                   0 <= i < N,
    {
        self.seq@[i]
    }

    pub open spec fn view(&self) -> Seq<Node>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

    pub open spec fn is_unique(&self) -> bool{
        forall|i: int, j:int| #![auto] i != j && 0<= i < N &&  0<= j < N ==> self.seq@[i].ptr != self.seq@[j].ptr
    }

}


}