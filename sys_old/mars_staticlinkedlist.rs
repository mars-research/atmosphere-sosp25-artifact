// https://verus-lang.github.io/verus/guide

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

pub struct MarsStaticLinkedList<const N: usize>{
    pub spec_seq: Ghost<Seq<Pointer>>,

    pub pointer_list: Ghost<Seq<Index>>,
    pub pointer_list_head: Index,
    pub pointer_list_tail: Index,
    pub pointer_list_len: usize,
    pub free_list: Ghost<Seq<Index>>,
    pub free_list_head: Index,
    pub free_list_tail: Index,
    pub free_list_len: usize,

    pub size: usize,


    pub arr_seq: Ghost<Seq<Node>>,
    pub ar: [Node;N],
}

impl<const N: usize> MarsStaticLinkedList<N> {

    pub open spec fn spec_len(&self) -> usize{
        self.pointer_list_len
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.pointer_list_len,
    {
        self.pointer_list_len
    }

    pub open spec fn is_unique(&self) -> bool {
        forall|i:int, j:int| #![auto] i != j && 0 <= i < self.spec_seq@.len() && 0 <= j < self.spec_seq@.len()
            ==> self.spec_seq@[i] != self.spec_seq@[j]
    }

    pub open spec fn view(&self) -> Seq<Pointer>
        recommends self.wf(),
    {
        self.spec_seq@
    }

    pub open spec fn prev_free_node_of(&self, i: nat) -> int
        recommends i < self.free_list@.len()
    {
        if i == 0{
            -1
        } else {
            self.free_list@[i - 1int] as int
        }
    }

    pub open spec fn next_free_node_of(&self, i: nat) -> int
        recommends i < self.free_list@.len()
    {
        if i + 1 == self.free_list@.len() {
            -1
        } else {
            self.free_list@[i + 1int] as int
        }
    }

    pub open spec fn wf_free_node_head(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_head == -1
        } else {
            self.free_list_head == self.free_list@[0]
        }
    }

    pub open spec fn wf_free_node_tail(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_tail == -1
        } else {
            self.free_list_tail  == self.free_list@[self.free_list@.len() - 1]
        }
    }

    pub open spec fn free_list_wf(&self) -> bool{
        (forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i))
        &&
        (forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i))
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) )
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) )
        &&
        (forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) )
        &&
        self.wf_free_node_head()
        &&
        self.wf_free_node_tail()
        &&
        self.free_list_len == self.free_list@.len()

    }

    pub open spec fn prev_pointer_node_of(&self, i: int) -> int
        recommends 0 <= i < self.pointer_list@.len()
    {
        if i == 0{
            -1
        } else {
            self.pointer_list@[i - 1int] as int
        }
    }

    pub open spec fn next_pointer_node_of(&self, i: int) -> int
        recommends 0 <= i < self.pointer_list@.len()
    {
        if i + 1 == self.pointer_list@.len() {
            -1
        } else {
            self.pointer_list@[i + 1int] as int
        }
    }

    pub open spec fn wf_pointer_node_head(&self) -> bool {
        if self.pointer_list@.len() == 0 {
            self.pointer_list_head == -1
        } else {
            self.pointer_list_head == self.pointer_list@[0]
        }
    }

    pub open spec fn wf_pointer_node_tail(&self) -> bool {
    if self.pointer_list@.len() == 0 {
        self.pointer_list_tail == -1
    } else {
        self.pointer_list_tail  == self.pointer_list@[self.pointer_list@.len() - 1]
    }
    }

    pub open spec fn pointer_list_wf(&self) -> bool{
        (forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i))
        &&
        (forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i))
        &&
        (forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) )
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) )
        &&
        (forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.pointer_list@.len() && 0 <= j < self.pointer_list@.len() ==> (self.pointer_list@[i as int] != self.pointer_list@[j as int]) )
        &&
        self.wf_pointer_node_head()
        &&
        self.wf_pointer_node_tail()
        &&
        self.pointer_list_len == self.pointer_list@.len()
    }

    pub open spec fn free_list_ptr_all_null(&self) -> bool
    {
        forall|i: Index| #![auto] 0 <= i < N && self.arr_seq@[i as int].ptr != NULL_POINTER ==> self.pointer_list@.contains(i)
    }

    pub open spec fn array_wf(&self) -> bool{
        self.arr_seq@.len() == N
        &&
        self.size == N
    }

    pub open spec fn wf_spec_seq(&self) -> bool
    {
        self.spec_seq@.len() == self.pointer_list_len
        &&
        forall|i:int| #![auto] 0<= i < self.pointer_list_len ==> self.arr_seq@[self.pointer_list@[i as int] as int].ptr == self.spec_seq@[i as int]
        
    }

    pub open spec fn wf(&self) -> bool{
        (self.array_wf())
        &&
        (self.free_list_len + self.pointer_list_len == N)
        &&
        (self.pointer_list_wf())
        &&
        (self.free_list_wf())
        &&
        (forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i))
        &&
        (self.wf_spec_seq())
        &&
        (self.free_list_ptr_all_null())
    }

    #[verifier(external_body)]
    fn set_ptr(&mut self, index: Index, v: Pointer)
        requires
            old(self).array_wf(),
        ensures 
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==> 
                self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==> 
                self.arr_seq@[i].ptr == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.pointer_list@ == old(self).pointer_list@,
            self.free_list@ == old(self).free_list@,
            self.pointer_list_head == old(self).pointer_list_head,
            self.pointer_list_tail == old(self).pointer_list_tail,
            self.pointer_list_len == old(self).pointer_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
            old(self).free_list_wf() ==> self.free_list_wf(),
            old(self).pointer_list_wf() ==> self.pointer_list_wf(),
    {
        self.ar[index as usize].ptr = v;
    }

    #[verifier(external_body)]
    fn set_next(&mut self, index: Index, v: Index)
        requires
            old(self).array_wf(),
        ensures 
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==> 
                self.arr_seq@[i].next == old(self).arr_seq@[i].next,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==> 
                self.arr_seq@[i].next == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.pointer_list@ == old(self).pointer_list@,
            self.free_list@ == old(self).free_list@,
            self.pointer_list_head == old(self).pointer_list_head,
            self.pointer_list_tail == old(self).pointer_list_tail,
            self.pointer_list_len == old(self).pointer_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
    {
        self.ar[index as usize].next = v;
    }

    #[verifier(external_body)]
    fn set_prev(&mut self, index: Index, v: Index)
        requires
            old(self).array_wf(),
        ensures 
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr && self.arr_seq@[i].next == old(self).arr_seq@[i].next,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==> 
                self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==> 
                self.arr_seq@[i].prev == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.pointer_list@ == old(self).pointer_list@,
            self.free_list@ == old(self).free_list@,
            self.pointer_list_head == old(self).pointer_list_head,
            self.pointer_list_tail == old(self).pointer_list_tail,
            self.pointer_list_len == old(self).pointer_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
    {
        self.ar[index as usize].next = v;
    }

    //TODO: prove this
    #[verifier(external_body)]
    pub fn put_ptr(&mut self, new_ptr: Pointer)
        requires
            old(self).array_wf(),
        ensures 
        self.array_wf(),
        forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
            self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev && self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
        self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
        self.pointer_list@ == old(self).pointer_list@,
        self.free_list@ == old(self).free_list@,
        self.pointer_list_head == old(self).pointer_list_head,
        self.pointer_list_tail == old(self).pointer_list_tail,
        self.pointer_list_len == old(self).pointer_list_len,
        self.free_list_head == old(self).free_list_head,
        self.free_list_tail == old(self).free_list_tail,
        self.free_list_len == old(self).free_list_len,
        old(self).free_list_wf() ==> self.free_list_wf(),
        old(self).pointer_list_wf() ==> self.pointer_list_wf(),
    {
        //self.spec_seq@ = self.spec_seq@.push(new_ptr);
    }


    pub open spec fn spec_get_ptr(&self, index: Index) -> (ptr:Pointer)
        recommends 
            self.wf(),
            0 <= index < N,
    {
        self.arr_seq@[index as int].ptr
    }

    #[verifier(external_body)]
    pub fn get_ptr(&self, index: Index) -> (ptr:Pointer)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            ptr == self.arr_seq@[index as int].ptr,
    {
        self.ar[index as usize].ptr
    }

    #[verifier(external_body)]
    pub fn get_next(&self, index: Index) -> (next:Index)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            next == self.arr_seq@[index as int].next,
    {
        self.ar[index as usize].next
    }

    #[verifier(external_body)]
    pub fn get_prev(&self, index: Index) -> (prev:Index)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            prev == self.arr_seq@[index as int].prev,
    {
        self.ar[index as usize].prev
    }
    

    #[verifier(inline)]
    pub open spec fn get_raw_element(&self, i: int) -> Node
        recommends self.arr_seq@.len() == N,
                   0 <= i < N,
    {
        self.arr_seq@[i]
    }

    //helper function for push()
    pub fn alloc_node_index(&mut self) -> (index: Index)
        requires old(self).pointer_list_len < old(self).size,
                 old(self).array_wf(),
                 old(self).free_list_len + old(self).pointer_list_len == N,
                 old(self).pointer_list_wf(),
                 old(self).free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i),
                old(self).wf_spec_seq(),
                old(self).free_list_ptr_all_null(),
        ensures self.free_list_len == old(self).free_list_len - 1,
                self.array_wf(),
                self.pointer_list_len ==  old(self).pointer_list_len,
                self.pointer_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.pointer_list@.contains(index) == false,
                self.wf_spec_seq(),          
                0 <= index < N,
                self.spec_seq == old(self).spec_seq,
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                    self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
                self.pointer_list@ == old(self).pointer_list@,
                self.free_list_ptr_all_null(),
    {
        assert(self.free_list_len > 0);
        assert(self.free_list@.len() > 0);

        //get the free node
        //assert(self.wf_free_node_head());
        assert(self.free_list_head != -1);
        assert(self.free_list_tail != -1);
        let mut node_index:Index = -1;
        if self.free_list_len == 1{
            assert(self.free_list_head == self.free_list_tail);
            node_index = self.free_list_head;
            self.free_list_head = -1;
            self.free_list_tail = -1;
            proof{self.free_list@ = self.free_list@.drop_last();}
            self.free_list_len = 0;
            assert(self.free_list_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).prev_pointer_node_of(i) == self.prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );
            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(self.pointer_list_len == self.pointer_list@.len());
            assert(self.pointer_list_wf());
        }else{
            assert(self.free_list_len > 1);
            assert(self.wf_free_node_head());
            assert(self.free_list_tail == self.free_list@[self.free_list@.len() - 1]);
            assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) != -1);
            assert(self.next_free_node_of((self.free_list@.len() - 1) as nat) == -1);
            node_index = self.free_list_tail;
            let next = self.get_next(self.free_list_tail);
            let prev = self.get_prev(self.free_list_tail);
            assert(next == -1);
            assert(prev != -1);
            assert(self.pointer_list@.contains(prev) == false);
            assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) == prev);
            assert(self.free_list@[self.free_list@.len() - 2 as int] == prev);
            self.set_next(prev, -1);
            assert(self.arr_seq@[prev as int].next == -1);
            proof{self.free_list@ = self.free_list@.drop_last();}
            self.free_list_len = self.free_list_len - 1;
            self.free_list_tail = prev;
            assert(self.free_list@.len() == self.free_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) ));
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(self.free_list_wf());

            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).prev_pointer_node_of(i) == self.prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );
            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(self.pointer_list_len == self.pointer_list@.len());
            assert(self.pointer_list_wf());
        }
        assert(self.free_list_wf());
        assert(self.pointer_list_wf());
        assert(self.free_list@.contains(node_index) == false);
        return node_index;
    }

    pub fn put_node_index(&mut self, index: Index, new_ptr:Pointer)
        requires
            old(self).array_wf(),
            old(self).pointer_list_wf(),
            old(self).free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i),
            old(self).free_list@.contains(index) == false,
            old(self).pointer_list@.contains(index) == false,
            old(self).wf_spec_seq(), 
            0 <= index < N,
            old(self).pointer_list_len < old(self).size,
        ensures
            self.free_list_len == old(self).free_list_len,
            self.array_wf(),
            self.pointer_list_wf(),
            self.free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
            self.free_list == old(self).free_list,
            self.pointer_list@ == old(self).pointer_list@.push(index),
            self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
            self.free_list_len == old(self).free_list_len,
            self.pointer_list_len == old(self).pointer_list_len + 1,
            self.wf_spec_seq(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==> 
                self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==> 
                self.arr_seq@[i].ptr == new_ptr,
    {

        // self.set_ptr(index, new_ptr);

        if self.pointer_list_len == 0{
            assert(self.pointer_list_head == -1);
            assert(self.pointer_list_tail == -1);
            self.pointer_list_head = index;
            self.pointer_list_tail = index;
            self.pointer_list_len = 1;
            self.set_prev(index, -1);
            self.set_next(index, -1);
            proof{self.pointer_list@ = self.pointer_list@.push(index);}
            assert(self.pointer_list@[0] == index);
            assert(self.pointer_list@.contains(index) == true);

            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(self.pointer_list_len == self.pointer_list@.len());
            assert(self.arr_seq@[index as int].next == -1);
            assert(self.arr_seq@[index as int].prev == -1);
            assert(self.next_pointer_node_of(0) == -1);
            assert(self.prev_pointer_node_of(0) == -1);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );

            assert(self.pointer_list_wf());


            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());
        }else{
            assert(self.pointer_list_wf());
            assert(self.pointer_list@.len() > 0);
            assert(self.pointer_list_tail != -1);

            assert(self.pointer_list_tail == self.pointer_list@[self.pointer_list@.len() - 1]);
            // assert(self.prev_pointer_node_of((self.pointer_list@.len() - 1) as nat) != -1);
            assert(self.next_pointer_node_of((self.pointer_list@.len() - 1) as int) == -1);
            assert(self.arr_seq@[self.pointer_list@[self.pointer_list@.len() - 1] as int].next == -1);
            let tail_index = self.pointer_list_tail;
            let prev = self.get_prev(tail_index);
            let next = self.get_next(tail_index);
            assert(next == -1);

            self.set_next(tail_index, index);
            self.set_prev(index, tail_index);
            self.set_next(index, -1);
            proof{self.pointer_list@ = self.pointer_list@.push(index);}
            assert(self.pointer_list@[self.pointer_list@.len() - 1] == index);
            assert(self.pointer_list@.contains(index) == true);
            self.pointer_list_len = self.pointer_list_len + 1;
            self.pointer_list_tail = index;


            assert(self.free_list@.contains(tail_index) == false);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());

            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            // assert(self.pointer_list_len == self.pointer_list@.len());
            // assert(self.arr_seq@[index as int].next == -1);
            // assert(self.arr_seq@[index as int].prev == -1);
            // assert(self.next_pointer_node_of(0) == -1);
            // assert(self.prev_pointer_node_of(0) == -1);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() -2 ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() -2 ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() - 1 ==> old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev == self.arr_seq@[self.pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() - 1 ==> old(self).prev_pointer_node_of(i) == self.prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );
            assert(self.pointer_list_wf());
        }
        self.set_ptr(index, new_ptr);
        self.put_ptr(new_ptr);
        assert(self.free_list_wf());
        assert(self.pointer_list_wf());
        assert(self.wf_spec_seq());
        assert(self.free_list@.contains(index) == false);
        assert(self.pointer_list@.contains(index) == true);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
    }
        

    pub fn push(&mut self, new_ptr: Pointer) -> (free_node_index : Index)
        requires old(self).wf(),
                 old(self).pointer_list_len < old(self).size,
                 old(self).is_unique(),
                 old(self).spec_seq@.contains(new_ptr) == false,
        ensures self.wf(),
                self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
                self.pointer_list@ == old(self).pointer_list@.push(free_node_index),
                self.pointer_list_len == old(self).pointer_list_len + 1,
                self.arr_seq@[free_node_index as int].ptr == new_ptr,
                self.spec_get_ptr(free_node_index) == new_ptr,
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != free_node_index ==> 
                    self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == free_node_index ==> 
                    self.arr_seq@[i].ptr == new_ptr,
                0 <= free_node_index < N,
                self.is_unique(),
                forall| ptr: Pointer| ptr != new_ptr ==> old(self).spec_seq@.contains(ptr) == self.spec_seq@.contains(ptr),
                self.spec_seq@.contains(new_ptr),
    {
        assert(self.wf_spec_seq());
        let free_node_index = self.alloc_node_index();
        assert(self.free_list_len == old(self).free_list_len - 1); 
        assert(self.array_wf()); 
        assert(self.pointer_list_len ==  old(self).pointer_list_len); 
        assert(self.pointer_list_wf()); 
        assert(self.free_list_wf()); 
        assert(forall|i:Index| #![auto] 0<= i < N && i != free_node_index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i)); 
        assert(self.free_list@.contains(free_node_index) == false); 
        assert(self.pointer_list@.contains(free_node_index) == false); 
        assert(self.wf_spec_seq());
        self.put_node_index(free_node_index, new_ptr);
        assert(self.free_list_len == old(self).free_list_len - 1); 
        assert(self.pointer_list_len ==  old(self).pointer_list_len + 1); 
        assert(self.array_wf());
        assert(self.free_list_len + self.pointer_list_len == N);
        assert(self.pointer_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        assert(self.wf_spec_seq());
        assert(self.spec_seq@ == old(self).spec_seq@.push(new_ptr));
        assert(old(self).spec_seq@.ext_equal(self.spec_seq@.subrange(0,self.spec_seq@.len() - 1)));
        assert(forall| ptr: Pointer| old(self).spec_seq@.contains(ptr) == self.spec_seq@.subrange(0,self.spec_seq@.len() - 1).contains(ptr));
        assert(forall| ptr: Pointer| ptr != new_ptr ==> old(self).spec_seq@.contains(ptr) == self.spec_seq@.contains(ptr));
        assert(self.spec_seq@[self.spec_seq@.len() as int - 1] == new_ptr);
        assert(self.spec_seq@.contains(new_ptr));
        return free_node_index;
    }

    //helper function for pop()
    pub fn pop_pointer(&mut self) -> (index: Index)
        requires old(self).pointer_list_len > 0,
                old(self).array_wf(),
                old(self).free_list_len + old(self).pointer_list_len == N,
                old(self).pointer_list_wf(),
                old(self).free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i),
                old(self).wf_spec_seq(),
                //old(self).free_list_ptr_all_null(),
        ensures self.free_list_len == old(self).free_list_len,
                self.array_wf(),
                self.pointer_list_len ==  old(self).pointer_list_len - 1,
                self.pointer_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.pointer_list@.contains(index) == false,
                self.spec_seq@ == old(self).spec_seq@.subrange(1,old(self).spec_seq@.len() as int), 
                self.wf_spec_seq(),       
                0 <= index < N,
                self.pointer_list@ == old(self).pointer_list@.subrange(1,old(self).pointer_list@.len() as int),
                index == old(self).pointer_list@[0],
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                    self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
                forall|i:Index| #![auto] i != index ==> 
                    old(self).pointer_list@.contains(i) == self.pointer_list@.contains(i),
                //self.free_list_ptr_all_null(),
    {
        assert(self.pointer_list_head != -1);
        assert(self.pointer_list_tail != -1);
        let mut node_index:Index = -1;
        if self.pointer_list_len == 1{
            assert(self.pointer_list_head == self.pointer_list_tail);
            node_index = self.pointer_list_head;
            self.pointer_list_head = -1;
            self.pointer_list_tail = -1;
            proof{self.pointer_list@ = self.pointer_list@.subrange(1,self.pointer_list@.len() as int);
                  self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.pointer_list_len = 0;
            assert(self.pointer_list_wf());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.wf_spec_seq());
        }else{
            assert(self.pointer_list_len > 1);
            assert(self.wf_pointer_node_head());
            assert(self.pointer_list_head == self.pointer_list@[0]);
            assert(self.prev_pointer_node_of(0) == -1);
            assert(self.next_pointer_node_of(0) != -1);
            node_index = self.pointer_list_head;
            let next = self.get_next(self.pointer_list_head);
            let prev = self.get_prev(self.pointer_list_head);
            assert(next != -1);
            assert(prev == -1);
            assert(self.free_list@.contains(next) == false);
            assert(self.next_pointer_node_of(0) == next);
            assert(self.pointer_list@[1] == next);
            self.set_prev(next, -1);
            assert(self.arr_seq@[next as int].prev == -1);
            proof{self.pointer_list@ = self.pointer_list@.subrange(1,self.pointer_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.pointer_list_len = self.pointer_list_len - 1;
            self.pointer_list_head = next;
            assert(self.pointer_list@.len() == self.pointer_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) ));
            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i + 1) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 1 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 1 <= i < self.pointer_list@.len() ==> self.prev_pointer_node_of(i) == old(self).prev_pointer_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(self.pointer_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());
            
            assert(self.wf_spec_seq());
        }
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i));
        // assert(self.free_list@.contains(node_index) == false);
        // assert(self.pointer_list@.contains(node_index) == false);
        assert(self.free_list == old(self).free_list);
        assert(self.pointer_list == old(self).pointer_list@.subrange(1,old(self).pointer_list@.len() as int));
        assert(node_index == old(self).pointer_list@[0]);
        assert(old(self).pointer_list@.index_of(node_index) == 0);
        assert(0<= node_index < N);
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));
        assert(old(self).pointer_list@.contains(node_index) && !self.pointer_list@.contains(node_index));

        assert(forall|i:Index| #![auto] 0<= i < N && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));

        assert(forall|i:int| #![auto] 0<= i <self.pointer_list@.len() ==> old(self).pointer_list@.index_of(self.pointer_list@[i]) == i + 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> old(self).pointer_list@[i] == self.pointer_list@[i - 1]);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i - 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> self.pointer_list@.contains(old(self).pointer_list@[i]));
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index && old(self).pointer_list@.contains(i) ==> self.pointer_list@.contains(i));

        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        return node_index;
    }

    fn free_node(&mut self, index: Index)
        requires
            old(self).array_wf(),
            old(self).pointer_list_wf(),
            old(self).free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i),
            old(self).free_list@.contains(index) == false,
            old(self).pointer_list@.contains(index) == false,
            old(self).wf_spec_seq(), 
            0 <= index < N,
            old(self).free_list_len < old(self).size,
        ensures
            self.array_wf(),
            self.pointer_list_wf(),
            self.free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
            self.wf_spec_seq(),
            self.free_list_len == old(self).free_list_len + 1,
            self.pointer_list_len == old(self).pointer_list_len,
            self.spec_seq == old(self).spec_seq,
            self.pointer_list == old(self).pointer_list,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
    {
        if self.free_list_len == 0{
            assert(self.free_list_head == -1);
            assert(self.free_list_tail == -1);
            self.free_list_head = index;
            self.free_list_tail = index;
            self.free_list_len = 1;
            self.set_prev(index, -1);
            self.set_next(index, -1);
            proof{self.free_list@ = self.free_list@.push(index);}
            assert(self.free_list@[0] == index);
            assert(self.free_list@.contains(index) == true);
        
            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.arr_seq@[index as int].next == -1);
            assert(self.arr_seq@[index as int].prev == -1);
            assert(self.next_free_node_of(0) == -1);
            assert(self.prev_free_node_of(0) == -1);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
        
            assert(self.free_list_wf());


            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).prev_pointer_node_of(i) == self.prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );
            assert(self.pointer_list_wf());
        }else{
            assert(self.free_list_wf());
            assert(self.free_list@.len() > 0);
            assert(self.free_list_tail != -1);
        
            assert(self.free_list_tail == self.free_list@[self.free_list@.len() - 1]);
            // assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) != -1);
            assert(self.next_free_node_of((self.free_list@.len() - 1) as nat) == -1);
            assert(self.arr_seq@[self.free_list@[self.free_list@.len() - 1] as int].next == -1);
            let tail_index = self.free_list_tail;
            let prev = self.get_prev(tail_index);
            let next = self.get_next(tail_index);
            assert(next == -1);
        
            self.set_next(tail_index, index);
            self.set_prev(index, tail_index);
            self.set_next(index, -1);
            proof{self.free_list@ = self.free_list@.push(index);}
            assert(self.free_list@[self.free_list@.len() - 1] == index);
            assert(self.free_list@.contains(index) == true);
            self.free_list_len = self.free_list_len + 1;
            self.free_list_tail = index;
        
        
            assert(self.pointer_list@.contains(tail_index) == false);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).prev_pointer_node_of(i) == self.prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) );
            assert(self.pointer_list_wf());

            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            // assert(self.free_list_len == self.free_list@.len());
            // assert(self.arr_seq@[index as int].next == -1);
            // assert(self.arr_seq@[index as int].prev == -1);
            // assert(self.next_free_node_of(0) == -1);
            // assert(self.prev_free_node_of(0) == -1);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() -2 ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() -2 ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).arr_seq@[old(self).free_list@[i as int] as int].prev == self.arr_seq@[self.free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());
        }
        assert(self.free_list_wf());
        assert(self.pointer_list_wf());
        assert(self.wf_spec_seq());
        assert(self.free_list@.contains(index) == true);
        assert(self.pointer_list@.contains(index) == false);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));

    }

    

    pub fn pop(&mut self) -> (ret: Pointer)
        requires old(self).wf(),
                 old(self).pointer_list_len > 0,
                 old(self).is_unique(),
        ensures 
                self.wf(),
                self.pointer_list_len == old(self).pointer_list_len - 1,
                self.pointer_list@ == old(self).pointer_list@.subrange(1, old(self).pointer_list@.len() as int),
                self.spec_seq@ == old(self).spec_seq@.subrange(1, old(self).spec_seq@.len() as int),
                ret == old(self).spec_seq@[0],
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != old(self).pointer_list@[0]==> 
                    self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
                self.is_unique(),
                forall| ptr: Pointer| ptr != ret ==> old(self).spec_seq@.contains(ptr) == self.spec_seq@.contains(ptr),
                self.spec_seq@.contains(ret) == false,
        {
            assert(self.spec_seq@[0] == self.arr_seq@[self.pointer_list@[0] as int].ptr);
            let pop_index = self.pop_pointer();
            assert(0<=pop_index<N);
            assert(old(self).spec_seq@[0] == self.arr_seq@[pop_index as int].ptr);
            let ret = self.get_ptr(pop_index);
            assert(ret == old(self).spec_seq@[0]);
            self.set_ptr(pop_index, NULL_POINTER);
            assert(self.free_list_ptr_all_null());
            self.free_node(pop_index);
            assert(self.free_list_len == old(self).free_list_len + 1);
            assert(self.pointer_list_len == old(self).pointer_list_len - 1);
            assert(self.wf());

            assert(old(self).is_unique());
            assert(ret == old(self).spec_seq@[0]);
            assert(self.spec_seq@ == old(self).spec_seq@.subrange(1, old(self).spec_seq@.len() as int));
            assert(forall| i: int| 0<= i <self.spec_seq@.len() ==> self.spec_seq@[i] == old(self).spec_seq@[i+1]);
            assert(forall| pointer:Pointer|  #![auto] self.spec_seq@.contains(pointer)  ==> self.spec_seq@.index_of(pointer) == old(self).spec_seq@.index_of(pointer) - 1);
            assert(forall| pointer:Pointer|  #![auto] self.spec_seq@.contains(pointer)  ==> old(self).spec_seq@.contains(pointer));
            assert(forall| i: int| 1 <= i <self.spec_seq@.len() + 1 ==>old(self).spec_seq@[i] == self.spec_seq@[i-1] );
            assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) &&  ret != pointer ==> self.spec_seq@.contains(pointer));


            // assert(old(self).arr_seq@[old(self).pointer_list@[ghost_index@ as int] as int].ptr == old(self).spec_seq@[ghost_index@ as int]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ret);
            // assert(ghost_index@ == old(self).spec_seq@.index_of(ret));
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) &&  ret != pointer ==> self.spec_seq@.contains(pointer));
            assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) == false  ==> self.spec_seq@.contains(pointer) == false);

            assert(forall| pointer:Pointer|  #![auto]  ret != pointer ==> old(self).spec_seq@.contains(pointer) == self.spec_seq@.contains(pointer));
            return ret;
        }

    fn remove_pointer_by_index_helper1(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).pointer_list@.contains(index),
                 old(self).pointer_list_head == index,
        ensures self.free_list_len == old(self).free_list_len,
                 self.array_wf(),
                 self.pointer_list_len ==  old(self).pointer_list_len - 1,
                 self.pointer_list_wf(),
                 self.free_list_wf(),
                 forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
                 self.free_list@.contains(index) == false,
                 self.pointer_list@.contains(index) == false,
                 self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)), 
                 self.wf_spec_seq(),       
                 0 <= index < N,
                 self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)),
                 forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                     self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
    {
        assert(self.pointer_list_head != -1);
        assert(self.pointer_list_tail != -1);
        if self.pointer_list_len == 1{
            assert(self.pointer_list_head == self.pointer_list_tail);
            self.pointer_list_head = -1;
            self.pointer_list_tail = -1;
            proof{self.pointer_list@ = self.pointer_list@.subrange(1,self.pointer_list@.len() as int);
                  self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.pointer_list_len = 0;
            assert(self.pointer_list_wf());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.wf_spec_seq());
        }else{
            assert(self.pointer_list_len > 1);
            assert(self.wf_pointer_node_head());
            assert(self.pointer_list_head == self.pointer_list@[0]);
            assert(self.prev_pointer_node_of(0) == -1);
            assert(self.next_pointer_node_of(0) != -1);
            let next = self.get_next(self.pointer_list_head);
            let prev = self.get_prev(self.pointer_list_head);
            assert(next != -1);
            assert(prev == -1);
            assert(self.free_list@.contains(next) == false);
            assert(self.next_pointer_node_of(0) == next);
            assert(self.pointer_list@[1] == next);
            self.set_prev(next, -1);
            assert(self.arr_seq@[next as int].prev == -1);
            proof{self.pointer_list@ = self.pointer_list@.subrange(1,self.pointer_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.pointer_list_len = self.pointer_list_len - 1;
            self.pointer_list_head = next;
            assert(self.pointer_list@.len() == self.pointer_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) ));
            assert(self.wf_pointer_node_head());
            assert(self.wf_pointer_node_tail());
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> old(self).next_pointer_node_of(i + 1) == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 1 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 1 <= i < self.pointer_list@.len() ==> self.prev_pointer_node_of(i) == old(self).prev_pointer_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(self.pointer_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());
            
            assert(self.wf_spec_seq());
        }
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).pointer_list@.contains(i));
        // assert(self.free_list@.contains(node_index) == false);
        // assert(self.pointer_list@.contains(node_index) == false);
        assert(self.free_list == old(self).free_list);
        assert(self.pointer_list == old(self).pointer_list@.subrange(1,old(self).pointer_list@.len() as int));
        assert(index == old(self).pointer_list@[0]);
        assert(old(self).pointer_list@.index_of(index) == 0);
        assert(0<= index < N);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));
        assert(old(self).pointer_list@.contains(index) && !self.pointer_list@.contains(index));

        assert(forall|i:Index| #![auto] 0<= i < N && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));

        assert(forall|i:int| #![auto] 0<= i <self.pointer_list@.len() ==> old(self).pointer_list@.index_of(self.pointer_list@[i]) == i + 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> old(self).pointer_list@[i] == self.pointer_list@[i - 1]);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i - 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> self.pointer_list@.contains(old(self).pointer_list@[i]));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index && old(self).pointer_list@.contains(i) ==> self.pointer_list@.contains(i));

        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));

        assert(self.free_list_len == old(self).free_list_len);
        assert(self.array_wf());
        assert(self.pointer_list_len ==  old(self).pointer_list_len - 1);
        assert(self.pointer_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        assert(self.free_list@.contains(index) == false);
        assert(self.pointer_list@.contains(index) == false);

        assert(old(self).spec_seq@.len() == old(self).pointer_list@.len());
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(1, old(self).pointer_list@.len() as int));
        assert(old(self).pointer_list@.index_of(index) == 0);
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(1,old(self).pointer_list@.len() as int));
        assert(Seq::<Pointer>::empty().len() == 0);
        assert(self.spec_seq@.ext_equal(Seq::<Pointer>::empty().add(old(self).spec_seq@.subrange(1,old(self).pointer_list@.len() as int))));
        assert(old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).len() == 0);
        assert( old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).ext_equal(Seq::<Pointer>::empty()));
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
        assert(self.wf_spec_seq());      
        assert(0 <= index < N);
        assert(self.pointer_list@ == old(self).pointer_list@.subrange(1, old(self).pointer_list@.len() as int));
        assert(old(self).pointer_list@.index_of(index) == 0);
        assert(self.pointer_list@ == old(self).pointer_list@.subrange(1,old(self).pointer_list@.len() as int));
        assert(Seq::<Index>::empty().len() == 0);
        assert(self.pointer_list@.ext_equal(Seq::<Index>::empty().add(old(self).pointer_list@.subrange(1,old(self).pointer_list@.len() as int))));
        assert(old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).len() == 0);
        assert( old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).ext_equal(Seq::<Index>::empty()));
        assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
        assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr);
    }

    fn remove_pointer_by_index_helper2(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).pointer_list@.contains(index),
                 old(self).pointer_list_head != index,
                 old(self).pointer_list_tail == index,
        ensures self.free_list_len == old(self).free_list_len,
                 self.array_wf(),
                 self.pointer_list_len ==  old(self).pointer_list_len - 1,
                 self.pointer_list_wf(),
                 self.free_list_wf(),
                 forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
                 self.free_list@.contains(index) == false,
                 self.pointer_list@.contains(index) == false,
                 self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)), 
                 self.wf_spec_seq(),       
                 0 <= index < N,
                 self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)),
                 forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                     self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
    {
        assert(self.pointer_list_tail != self.pointer_list_head);
        assert(self.pointer_list_len > 1);

        assert(self.pointer_list_len > 1);
        assert(self.wf_pointer_node_head());
        assert(self.pointer_list_tail == self.pointer_list@[self.pointer_list@.len() - 1]);
        assert(self.prev_pointer_node_of((self.pointer_list@.len() - 1) as int) != -1);
        assert(self.next_pointer_node_of((self.pointer_list@.len() - 1) as int) == -1);
        let next = self.get_next(self.pointer_list_tail);
        let prev = self.get_prev(self.pointer_list_tail);
        assert(next == -1);
        assert(prev != -1);
        assert(self.free_list@.contains(prev) == false);
        assert(self.prev_pointer_node_of((self.pointer_list@.len() - 1) as int) == prev);
        assert(self.pointer_list@[self.pointer_list@.len() - 2 as int] == prev);
        self.set_next(prev, -1);
        assert(self.arr_seq@[prev as int].next == -1);
        proof{self.pointer_list@ = self.pointer_list@.drop_last();
            self.spec_seq@ = self.spec_seq@.drop_last();
        }
        self.pointer_list_len = self.pointer_list_len - 1;
        assert(self.wf_spec_seq());
        self.pointer_list_tail = prev;
        assert(self.pointer_list@.len() == self.pointer_list_len);
        assert((forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] < N) ));
        assert((forall|i: int|  #![auto] 0 <= i < self.pointer_list@.len() ==> (self.pointer_list@[i as int] >= 0) ));
        assert(self.wf_pointer_node_head());
        assert(self.wf_pointer_node_tail());
        assert(self.pointer_list_len == self.pointer_list@.len());
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() - 1 ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() - 1 ==> old(self).next_pointer_node_of(i) == self.next_pointer_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.prev_pointer_node_of(i) == old(self).prev_pointer_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
        assert(self.pointer_list_wf());

        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
        assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
        assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
        assert(self.wf_free_node_head());
        assert(self.wf_free_node_tail());
        assert(self.free_list_len == self.free_list@.len());
        assert(self.free_list_wf());

        assert(self.free_list@.contains(index) == false);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));

        assert(self.free_list_len == old(self).free_list_len);
        assert(self.array_wf());
        assert(self.pointer_list_len ==  old(self).pointer_list_len - 1);
        assert(self.pointer_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        assert(self.free_list@.contains(index) == false);
        assert(self.pointer_list@.contains(index) == false);
        
        assert(old(self).spec_seq@.len() == old(self).pointer_list@.len());
        assert(self.spec_seq@ == old(self).spec_seq@.drop_last());
        assert(old(self).pointer_list@.index_of(index) == old(self).pointer_list@.len() - 1);
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)));
        assert(Seq::<Pointer>::empty().len() == 0);
        assert(self.spec_seq@.ext_equal(old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(Seq::<Pointer>::empty())));
        assert(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int).len() == 0);
        assert(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int).ext_equal(Seq::<Pointer>::empty()));

        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
        
        assert(self.wf_spec_seq());      
        assert(0 <= index < N);
        assert(self.pointer_list@ == old(self).pointer_list@.drop_last());
        assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)));
        assert(Seq::<Index>::empty().len() == 0);
        assert(self.pointer_list@.ext_equal(old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(Seq::<Index>::empty())));
        assert(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int).len() == 0);
        assert(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int).ext_equal(Seq::<Index>::empty()));
        assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
        assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr);
    }

    fn remove_pointer_by_index_helper3(&mut self, index: Index)
    requires old(self).wf(),
             old(self).pointer_list@.contains(index),
             old(self).pointer_list_head != index,
             old(self).pointer_list_tail != index,
    ensures self.free_list_len == old(self).free_list_len,
             self.array_wf(),
             self.pointer_list_len ==  old(self).pointer_list_len - 1,
             self.pointer_list_wf(),
             self.free_list_wf(),
             forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
             self.free_list@.contains(index) == false,
             self.pointer_list@.contains(index) == false,
             self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)), 
             self.wf_spec_seq(),       
             0 <= index < N,
             self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)),
             forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                 self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
    {
        assert(self.pointer_list_tail != self.pointer_list_head);
        assert(self.pointer_list_tail != index);
        assert(self.pointer_list_head != index);
        assert(self.pointer_list@.contains(index));
        assert(self.pointer_list@.contains(self.pointer_list_head));
        assert(self.pointer_list@.contains(self.pointer_list_tail));
        assert(self.pointer_list@.len() >= 3);

        let prev = self.get_prev(index);
        let next = self.get_next(index);
        let index_in_list:Ghost<int> = Ghost(self.pointer_list@.index_of(index));
        proof{
            //let index_in_list = self.pointer_list@.index_of(index);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(prev == self.arr_seq@[self.pointer_list@[index_in_list@ as int] as int].prev);
            assert(next == self.arr_seq@[self.pointer_list@[index_in_list@ as int] as int].next);
            assert(self.next_pointer_node_of(index_in_list@) == next);
            assert(self.prev_pointer_node_of(index_in_list@) == prev);
        }
        assert(self.free_list@.contains(index) == false);
        assert(self.free_list@.contains(prev) == false);
        assert(self.free_list@.contains(next) == false);
        self.set_next(prev, next);
        self.set_prev(next, prev);
        self.pointer_list_len = self.pointer_list_len - 1;
        proof{
            self.pointer_list@ = self.pointer_list@.subrange(0,index_in_list@).add(self.pointer_list@.subrange(index_in_list@ + 1, self.pointer_list@.len() as int));
            self.spec_seq@ = self.spec_seq@.subrange(0,index_in_list@).add(self.spec_seq@.subrange(index_in_list@ + 1, self.spec_seq@.len() as int));
            assert(self.pointer_list@[index_in_list@ as int] == next);
            assert(self.pointer_list@[index_in_list@ as int - 1] == prev);
            assert(self.next_pointer_node_of(index_in_list@ - 1) == next);
            assert(self.prev_pointer_node_of(index_in_list@) == prev);
            assert(prev == self.arr_seq@[self.pointer_list@[index_in_list@ as int] as int].prev);
            assert(next == self.arr_seq@[self.pointer_list@[index_in_list@ as int - 1] as int].next);
            assert(self.arr_seq@[self.pointer_list@[index_in_list@ as int] as int].prev == self.prev_pointer_node_of(index_in_list@));
            assert(self.arr_seq@[self.pointer_list@[index_in_list@ as int - 1] as int].next == self.next_pointer_node_of(index_in_list@ as int - 1));
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ - 1 ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ - 1 ==> self.next_pointer_node_of(i) == old(self).next_pointer_node_of(i));
            assert(forall|i: int| #![auto] index_in_list@ <= i < self.pointer_list@.len() ==> self.next_pointer_node_of(i) == old(self).next_pointer_node_of(i + 1));
            assert(forall|i: int| #![auto] index_in_list@ <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].next == self.next_pointer_node_of(i));

            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ ==> self.prev_pointer_node_of(i) == old(self).prev_pointer_node_of(i));
            assert(forall|i: int| #![auto] index_in_list@ + 1 <= i < self.pointer_list@.len() ==> self.prev_pointer_node_of(i) == old(self).prev_pointer_node_of(i + 1));
            assert(forall|i: int| #![auto] index_in_list@ + 1 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == old(self).arr_seq@[old(self).pointer_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.pointer_list@.len() ==> self.arr_seq@[self.pointer_list@[i as int] as int].prev == self.prev_pointer_node_of(i));
            assert(self.pointer_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.wf_spec_seq());

            assert(index == old(self).pointer_list@[index_in_list@]);
            assert(old(self).pointer_list@.index_of(index) == index_in_list@);
            assert(0<= index < N);
            assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
            assert(forall|i:Index| #![auto] 0<= i < N && i != index && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));
            assert(old(self).pointer_list@.contains(index) && !self.pointer_list@.contains(index));
    
            assert(forall|i:Index| #![auto] 0<= i < N && !old(self).pointer_list@.contains(i) ==> !self.pointer_list@.contains(i));
    
            assert(forall|i:int| #![auto] 0<= i < index_in_list@ ==> old(self).pointer_list@.index_of(self.pointer_list@[i]) == i);
            assert(forall|i:int| #![auto] index_in_list@ <= i < self.pointer_list@.len() ==> old(self).pointer_list@.index_of(self.pointer_list@[i]) == i + 1);
            assert(forall|i:int| #![auto] 0<= i < index_in_list@ ==> old(self).pointer_list@[i] == self.pointer_list@[i]);
            assert(forall|i:int| #![auto] index_in_list@ + 1<= i < old(self).pointer_list@.len() ==> old(self).pointer_list@[i] == self.pointer_list@[i - 1]);
            // assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i - 1);
            // assert(forall|i:int| #![auto] 1<= i <old(self).pointer_list@.len() && i != index_in_list@ ==> self.pointer_list@.contains(old(self).pointer_list@[i]));
            assert(forall|i:Index| #![auto] 0<= i < N && i != index && old(self).pointer_list@.contains(i) ==> self.pointer_list@.contains(i));
    
            assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        }
        // assert(self.free_list_len == old(self).free_list_len);
        // assert(self.array_wf());
        // assert(self.pointer_list_len ==  old(self).pointer_list_len - 1);
        // assert(self.pointer_list_wf());
        // assert(self.free_list_wf());
        // assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i));
        // assert(self.free_list@.contains(index) == false);
        // assert(self.pointer_list@.contains(index) == false);
        // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
        // assert(self.wf_spec_seq());      
        // assert(0 <= index < N);
        // assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
        // assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr);
    }

    #[verifier(memoize)]
    pub fn remove_pointer_by_index(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).pointer_list@.contains(index),
        ensures self.free_list_len == old(self).free_list_len,
                self.array_wf(),
                self.pointer_list_len ==  old(self).pointer_list_len - 1,
                self.pointer_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.pointer_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.pointer_list@.contains(index) == false,
                self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)), 
                self.wf_spec_seq(),       
                0 <= index < N,
                self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)),
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                    self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
    {
        assert(self.pointer_list@.len() > 0);
        assert(self.pointer_list_len > 0);
        assert(self.pointer_list_head != -1);
        assert(self.pointer_list_tail != -1);
        assert(self.free_list@.contains(index) == false);
        if index == self.pointer_list_head {
            self.remove_pointer_by_index_helper1(index);
        }else if index == self.pointer_list_tail{
            self.remove_pointer_by_index_helper2(index);
        }else{
            self.remove_pointer_by_index_helper3(index);
        }
    }


    pub fn remove(&mut self, index: Index) -> (ret: Pointer)
        requires old(self).wf(),
                 old(self).pointer_list@.contains(index),
                 old(self).is_unique(),
        ensures self.wf(),
                self.pointer_list_len == old(self).pointer_list_len - 1,
                ret == old(self).arr_seq@[index as int].ptr,
                self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)), 
                self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)),
                // forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) && old(self).spec_get_ptr(index) != pointer ==> self.spec_seq@.contains(pointer),
                // self.spec_seq@.contains(old(self).spec_get_ptr(index)) == false,
                forall| pointer:Pointer|  #![auto]  ret != pointer ==> old(self).spec_seq@.contains(pointer) == self.spec_seq@.contains(pointer),
                    self.spec_seq@.contains(ret) == false,
                forall| _index: Index|  #![auto]  index != _index ==> old(self).pointer_list@.contains(_index) == self.pointer_list@.contains(_index),
                    self.pointer_list@.contains(index) == false,
                self.is_unique(),
                // forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> 
                //     self.arr_seq@[i].ptr == old(self).arr_seq@[i].ptr,
                // forall| ptr: Pointer| ptr != ret ==> old(self).spec_seq@.contains(ptr) == self.spec_seq@.contains(ptr),
                // self.spec_seq@.contains(ret),
        {
            self.remove_pointer_by_index(index);
            let ret = self.get_ptr(index);
            self.set_ptr(index, NULL_POINTER);
            // assert(self.arr_seq@[index as int].ptr == NULL_POINTER);
            // assert( forall|i: Index| #![auto] 0 <= i < N && i != index ==> self.arr_seq@[i as int].ptr == old(self).arr_seq@[i as int].ptr);
            // assert( forall|i: Index| #![auto] old(self).pointer_list@.contains(i) && i != index ==> self.pointer_list@.contains(i));
            // assert( forall|i: Index| #![auto] 0 <= i < N && self.arr_seq@[i as int].ptr != NULL_POINTER ==> self.pointer_list@.contains(i));
            let ghost_index:Ghost<int> = Ghost(old(self).pointer_list@.index_of(index));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.len() && i != ghost_index@ ==> old(self).pointer_list@[i] != index);
            // assert(ghost_index@ == old(self).pointer_list@.index_of(index));
            // assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.index_of(index) ==> self.pointer_list@[i] == old(self).pointer_list@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.index_of(index) ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).pointer_list@.index_of(index)  < i < old(self).pointer_list@.len() ==> self.pointer_list@[i - 1] == old(self).pointer_list@[i]);
            // assert(forall|i:int|#![auto] old(self).pointer_list@.index_of(index)  < i < old(self).pointer_list@.len() ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i - 1);

            // assert(forall| _index:Index|  #![auto] old(self).pointer_list@.contains(_index) &&  index != _index ==> self.pointer_list@.contains(_index));
            // assert(forall| _index:Index|  #![auto] old(self).pointer_list@.contains(_index) == false  ==> self.pointer_list@.contains(_index) == false);

            // assert(forall| _index:Index|  #![auto]  index != _index ==> old(self).pointer_list@.contains(_index) == self.pointer_list@.contains(_index));
            // assert(self.free_list_ptr_all_null());

            // assert(self.pointer_list_len == old(self).pointer_list_len - 1);
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).spec_seq@.len() as int))); 
            // assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
            assert(ret == old(self).arr_seq@[index as int].ptr);


            self.free_node(index);

            // let ghost_index:Ghost<int> = ghost(old(self).pointer_list@.index_of(index));
            // let ghost_ptr:Ghost<Pointer> = ghost(old(self).spec_seq@[ghost_index@ as int]);
            // assert(old(self).arr_seq@[old(self).pointer_list@[ghost_index@ as int] as int].ptr == old(self).spec_seq@[ghost_index@ as int]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ghost_ptr@);
            // assert(ghost_index@ == old(self).spec_seq@.index_of(ghost_ptr@));
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            // assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) &&  ghost_ptr@ != pointer ==> self.spec_seq@.contains(pointer));
            assert(old(self).arr_seq@[old(self).pointer_list@[ghost_index@ as int] as int].ptr == old(self).spec_seq@[ghost_index@ as int]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ret);
            assert(ghost_index@ == old(self).spec_seq@.index_of(ret));
            assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) &&  ret != pointer ==> self.spec_seq@.contains(pointer));
            assert(forall| pointer:Pointer|  #![auto] old(self).spec_seq@.contains(pointer) == false  ==> self.spec_seq@.contains(pointer) == false);

            assert(forall| pointer:Pointer|  #![auto]  ret != pointer ==> old(self).spec_seq@.contains(pointer) == self.spec_seq@.contains(pointer));

            assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.len() && i != ghost_index@ ==> old(self).pointer_list@[i] != index);
            assert(ghost_index@ == old(self).pointer_list@.index_of(index));
            assert(self.pointer_list@ == old(self).pointer_list@.subrange(0,old(self).pointer_list@.index_of(index)).add(old(self).pointer_list@.subrange(old(self).pointer_list@.index_of(index) + 1, old(self).pointer_list@.len() as int)));
            assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.index_of(index) ==> self.pointer_list@[i] == old(self).pointer_list@[i]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).pointer_list@.index_of(index) ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i);
            assert(forall|i:int|#![auto] old(self).pointer_list@.index_of(index)  < i < old(self).pointer_list@.len() ==> self.pointer_list@[i - 1] == old(self).pointer_list@[i]);
            assert(forall|i:int|#![auto] old(self).pointer_list@.index_of(index)  < i < old(self).pointer_list@.len() ==> self.pointer_list@.index_of(old(self).pointer_list@[i]) == i - 1);

            assert(forall| _index:Index|  #![auto] old(self).pointer_list@.contains(_index) &&  index != _index ==> self.pointer_list@.contains(_index));
            assert(self.wf());
            return ret;
        }

    // fn test(sll: &mut MarsStaticLinkedList<2>)
    //     requires 
    //         old(sll).wf(),
    //         old(sll).arr_seq@.len() == 2,
    //         old(sll).get_raw_element(0).next == 0,

    // {
    //     assert(sll.get_raw_element(0).next == 0);
    //     sll.set_ptr(0,0x10);
    //     assert(sll.get_raw_element(0).ptr == 0x10);
    //     assert(sll.get_raw_element(0).next == 0);
    // }

}

}