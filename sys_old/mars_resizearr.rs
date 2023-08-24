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
use super::Node;

pub const MAX_BLOCKS: usize = 512;
pub const NODE_PER_BLOCK: usize = 128;

verus! {
    #[verifier(external_body)]
    proof fn lemma_unique_pptr(seq: Seq<usize>, v: usize)
        ensures
            seq.contains(v) == false,
            v != 0,
    {
        unimplemented!();
    }
    #[verifier(external_body)]
    proof fn lemma_same_raw_ptr(ptr1 :int, ptr2 :int)
        ensures
            ptr1 == ptr2,
    {
        unimplemented!();
    }
pub struct MarsResizeArray{
    pub spec_seq: Ghost<Seq<Node>>,
    pub capacity: usize,
    //pub block_size: usize,
    pub num_block: usize,
    pub block_perms: Tracked<Map<int, PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>>>>,


    pub block_ptrs:MarsArray<usize, MAX_BLOCKS>, // we use one page for metadata
}

impl MarsResizeArray {

    pub open spec fn wf(&self) -> bool
    {
        self.num_block <= MAX_BLOCKS
        &&
        self.capacity == NODE_PER_BLOCK * self.num_block
        &&
        self.capacity == self.spec_seq@.len()
        &&
        self.block_ptrs.wf()
        &&
        self.block_ptrs.is_unique()
        &&
        (forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_ptrs@[i] != NULL_POINTER)
        &&
        (forall |i: int|#![auto] self.num_block<= i < MAX_BLOCKS ==> self.block_ptrs@[i] == NULL_POINTER)
        &&
        (forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@.dom().contains(self.block_ptrs@[i] as int))
        &&
        (forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().pptr == self.block_ptrs@[i] as int)
        &&
        (forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.is_Some())
        &&
        (forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0().wf())
        &&
        (forall |i: int, j: int| #![auto] 0<= i < self.num_block && 0<= j < NODE_PER_BLOCK ==> self.spec_seq@[i * NODE_PER_BLOCK + j] 
                == self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0()@[j])
    }

    // #[verifier(external_body)]
    pub fn get_prev(&mut self, index: Index) -> (prev:Index)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.spec_seq == old(self).spec_seq,
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            prev == old(self).spec_seq@[index as int].prev,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        let prev = block.get(block_index).prev;
        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(prev == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev);
        return prev;
    }
    pub fn get_next(&mut self, index: Index) -> (next:Index)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.spec_seq == old(self).spec_seq,
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            next == old(self).spec_seq@[index as int].next,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        let next = block.get(block_index).next;
        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(next == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next);
        return next;
    }

    pub fn get_ptr(&mut self, index: Index) -> (ptr:Pointer)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.spec_seq == old(self).spec_seq,
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            ptr == old(self).spec_seq@[index as int].ptr,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        let ptr = block.get(block_index).ptr;
        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(ptr == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr);
        return ptr;
    }

        // #[verifier(external_body)]
    pub fn set_prev(&mut self, index: Index, new_prev:Index)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            forall |i: int|#![auto] 0<= i < self.capacity && i != index ==> self.spec_seq@[i] == old(self).spec_seq@[i],
            self.spec_seq@[index as int].next == old(self).spec_seq@[index as int].next,
            self.spec_seq@[index as int].ptr == old(self).spec_seq@[index as int].ptr,
            self.spec_seq@[index as int].prev == new_prev,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;       
        proof{
            let next = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next;
            let ptr = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr;
            self.spec_seq@ = self.spec_seq@.update(index as int, Node { next: next, ptr: ptr, prev: new_prev });
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        block.set_prev(block_index, new_prev);

        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        assert(new_prev == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr);
        assert(self.num_block <= MAX_BLOCKS);
        assert(self.capacity == NODE_PER_BLOCK * self.num_block);
        assert(self.capacity == self.spec_seq@.len());
        assert(self.block_ptrs.wf());
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_ptrs@[i] != NULL_POINTER));
        assert((forall |i: int|#![auto] self.num_block<= i < MAX_BLOCKS ==> self.block_ptrs@[i] == NULL_POINTER));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@.dom().contains(self.block_ptrs@[i] as int)));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().pptr == self.block_ptrs@[i] as int));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.is_Some()));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0().wf()));
        assert(forall |i: int| #![auto] 0<= i < self.capacity && i != index ==>( self.spec_seq@[i] 
            == old(self).spec_seq@[i]) );
        assert(self.block_ptrs@[block_number as int] == block_ptr);
        assert(forall |i: int| #![auto] 0<= i < self.num_block && i != block_number  ==> old(self).block_perms@[old(self).block_ptrs@[i] as int].view().value.get_Some_0()@.ext_equal(
            self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0()@));
    }

    //         // #[verifier(external_body)]
    pub fn set_next(&mut self, index: Index, new_next:Index)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            forall |i: int|#![auto] 0<= i < self.capacity && i != index ==> self.spec_seq@[i] == old(self).spec_seq@[i],
            self.spec_seq@[index as int].prev == old(self).spec_seq@[index as int].prev,
            self.spec_seq@[index as int].ptr == old(self).spec_seq@[index as int].ptr,
            self.spec_seq@[index as int].next == new_next,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;       
        proof{
            let prev = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev;
            let ptr = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr;
            self.spec_seq@ = self.spec_seq@.update(index as int, Node { next: new_next, ptr: ptr, prev: prev });
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        block.set_next(block_index, new_next);

        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        assert(new_next == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr);
        assert(self.num_block <= MAX_BLOCKS);
        assert(self.capacity == NODE_PER_BLOCK * self.num_block);
        assert(self.capacity == self.spec_seq@.len());
        assert(self.block_ptrs.wf());
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_ptrs@[i] != NULL_POINTER));
        assert((forall |i: int|#![auto] self.num_block<= i < MAX_BLOCKS ==> self.block_ptrs@[i] == NULL_POINTER));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@.dom().contains(self.block_ptrs@[i] as int)));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().pptr == self.block_ptrs@[i] as int));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.is_Some()));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0().wf()));
        assert(forall |i: int| #![auto] 0<= i < self.capacity && i != index ==>( self.spec_seq@[i] 
            == old(self).spec_seq@[i]) );
        assert(self.block_ptrs@[block_number as int] == block_ptr);
        assert(forall |i: int| #![auto] 0<= i < self.num_block && i != block_number  ==> old(self).block_perms@[old(self).block_ptrs@[i] as int].view().value.get_Some_0()@.ext_equal(
            self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0()@));
    }

    pub fn set_ptr(&mut self, index: Index, new_ptr:Pointer)
        requires
            0 <= index < old(self).capacity,
            old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.num_block == old(self).num_block,
            self.block_ptrs == old(self).block_ptrs,
            forall |i: int|#![auto] 0<= i < self.capacity && i != index ==> self.spec_seq@[i] == old(self).spec_seq@[i],
            self.spec_seq@[index as int].prev == old(self).spec_seq@[index as int].prev,
            self.spec_seq@[index as int].next == old(self).spec_seq@[index as int].next,
            self.spec_seq@[index as int].ptr == new_ptr,
    {
        let block_number = index as usize/NODE_PER_BLOCK;
        let block_index = index as usize%NODE_PER_BLOCK;       
        proof{
            let prev = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev;
            let next = self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next;
            self.spec_seq@ = self.spec_seq@.update(index as int, Node { next: next, ptr: new_ptr, prev: prev });
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        let block_ptr = *self.block_ptrs.get(block_number as usize);
        assert(block_ptr ==  self.block_ptrs@[block_number as int] as int);
        assert(self.block_perms@.dom().contains(block_ptr as int));
        let block_pptr = PPtr::<MarsNoderrayNode<NODE_PER_BLOCK>>::from_usize(block_ptr);
        assert(self.block_perms@[block_ptr as int].view().pptr == block_ptr as int);
        let tracked mut block_perm: PointsTo<MarsNoderrayNode<NODE_PER_BLOCK>> =
            (self.block_perms.borrow_mut()).tracked_remove(block_ptr as int);
        assert(block_perm@.pptr == block_ptr as int);
        assert(block_ptr as int == block_pptr.id());
        let mut block = block_pptr.take(Tracked(&mut block_perm));
        block.set_ptr(block_index, new_ptr);

        let (new_block_pptr, new_block_perm) = PPtr::new(block);
        proof {
            lemma_same_raw_ptr(new_block_pptr.id(), block_ptr as int);
            (self.block_perms.borrow_mut())
                .tracked_insert(block_ptr as int, (new_block_perm).get());
        }
        assert(0<= block_number < self.num_block );
        assert(0<= block_index < NODE_PER_BLOCK );
        assert(new_ptr == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].ptr);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].prev);
        assert(old(self).block_perms@[old(self).block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next == self.block_perms@[self.block_ptrs@[block_number as int] as int].view().value.get_Some_0()@[block_index as int].next);
        assert(self.num_block <= MAX_BLOCKS);
        assert(self.capacity == NODE_PER_BLOCK * self.num_block);
        assert(self.capacity == self.spec_seq@.len());
        assert(self.block_ptrs.wf());
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_ptrs@[i] != NULL_POINTER));
        assert((forall |i: int|#![auto] self.num_block<= i < MAX_BLOCKS ==> self.block_ptrs@[i] == NULL_POINTER));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@.dom().contains(self.block_ptrs@[i] as int)));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().pptr == self.block_ptrs@[i] as int));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.is_Some()));
        assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0().wf()));
        assert(forall |i: int| #![auto] 0<= i < self.capacity && i != index ==>( self.spec_seq@[i] 
            == old(self).spec_seq@[i]) );
        assert(self.block_ptrs@[block_number as int] == block_ptr);
        assert(forall |i: int| #![auto] 0<= i < self.num_block && i != block_number  ==> old(self).block_perms@[old(self).block_ptrs@[i] as int].view().value.get_Some_0()@.ext_equal(
            self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0()@));
    }

    pub fn grow(&mut self,new_block: MarsNoderrayNode<NODE_PER_BLOCK>)
        requires
            old(self).num_block < MAX_BLOCKS,
            old(self).wf(),
            new_block.wf(),
        ensures
            self.wf(),
            self.num_block == old(self).num_block + 1,
            self.capacity == old(self).capacity + NODE_PER_BLOCK,
            self.spec_seq@.subrange(0, old(self).capacity as int).ext_equal(old(self).spec_seq@),
        {
            assert(self.capacity <= (MAX_BLOCKS - 1) * NODE_PER_BLOCK);
            let mut i:usize = 0;
            while i != NODE_PER_BLOCK
                invariant
                    0<= i <= NODE_PER_BLOCK,
                    self.num_block == old(self).num_block,
                    old(self).spec_seq@.len() == old(self).capacity,
                    self.capacity == old(self).capacity + i,
                    self.capacity <= old(self).capacity + NODE_PER_BLOCK,
                    old(self).capacity <= (MAX_BLOCKS - 1) * NODE_PER_BLOCK,
                    self.capacity <= MAX_BLOCKS * NODE_PER_BLOCK,
                    self.spec_seq@.len() == old(self).spec_seq@.len() + i,
                    self.spec_seq@.len() >= old(self).spec_seq@.len(),
                    self.spec_seq@.subrange(0, old(self).capacity as int).ext_equal(old(self).spec_seq@),
                    forall|j: int| #![auto] 0<= j< i ==> self.spec_seq@[old(self).capacity as int + j] == new_block@[j],
                    new_block.wf(),
                    self.block_ptrs == old(self).block_ptrs,
                    self.block_perms == old(self).block_perms,
                ensures 
                    i == NODE_PER_BLOCK,
                    self.num_block == old(self).num_block,
                    old(self).spec_seq@.len() == old(self).capacity,
                    self.capacity == old(self).capacity + NODE_PER_BLOCK,
                    self.capacity <= old(self).capacity + NODE_PER_BLOCK,
                    old(self).capacity <= (MAX_BLOCKS - 1) * NODE_PER_BLOCK,
                    self.capacity <= MAX_BLOCKS * NODE_PER_BLOCK,
                    self.spec_seq@.len() == old(self).spec_seq@.len() + NODE_PER_BLOCK,
                    self.spec_seq@.len() >= old(self).spec_seq@.len(),
                    self.spec_seq@.subrange(0, old(self).capacity as int).ext_equal(old(self).spec_seq@),
                    forall|j: int| #![auto] 0<= j< NODE_PER_BLOCK ==> self.spec_seq@[old(self).capacity as int + j] == new_block@[j],
                    new_block.wf(),
                    self.block_ptrs == old(self).block_ptrs,
                    self.block_perms == old(self).block_perms,
            {
                assert(self.spec_seq@.len() >= old(self).capacity);
                assert(0<= i <= NODE_PER_BLOCK);
                self.capacity = self.capacity + 1;
                assert(forall|j: int| #![auto] 0<= j< i ==> self.spec_seq@[old(self).capacity as int + j] == new_block@[j]);
                proof{
                    self.spec_seq@ = self.spec_seq@.push(new_block@[i as int]);
                }
                assert(self.spec_seq@[old(self).capacity as int + i] == new_block@[i as int]);
                assert(forall|j: int| #![auto] 0<= j< i+1 ==> self.spec_seq@[old(self).capacity as int + j] == new_block@[j]);
                assert(self.spec_seq@.subrange(0, old(self).capacity as int).ext_equal(old(self).spec_seq@));
                i = i + 1;
            }

            let (new_block_pptr, new_block_perm) = PPtr::new(new_block);
            proof {
                (self.block_perms.borrow_mut())
                    .tracked_insert(new_block_pptr.id(), (new_block_perm).get());
            }
            let ptr = new_block_pptr.to_usize();
            self.num_block = self.num_block + 1;
            assert(0<= self.num_block <= MAX_BLOCKS);
            assert(self.block_ptrs.wf());
            proof{lemma_unique_pptr(self.block_ptrs@, ptr);}
            self.block_ptrs.set(self.num_block - 1, ptr);
            assert(self.block_ptrs.is_unique());
            assert(self.num_block <= MAX_BLOCKS);
            assert(self.capacity == NODE_PER_BLOCK * self.num_block);
            assert(self.capacity == self.spec_seq@.len());
            assert(self.block_ptrs.wf());
            assert(self.block_ptrs.is_unique());
            assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_ptrs@[i] != NULL_POINTER));
            assert((forall |i: int|#![auto] self.num_block<= i < MAX_BLOCKS ==> self.block_ptrs@[i] == NULL_POINTER));
            assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@.dom().contains(self.block_ptrs@[i] as int)));
            assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().pptr == self.block_ptrs@[i] as int));
            assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.is_Some()));
            assert((forall |i: int|#![auto] 0<= i < self.num_block ==> self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0().wf()));
            assert((forall |i: int, j: int| #![auto] 0<= i < self.num_block && 0<= j < NODE_PER_BLOCK ==> self.spec_seq@[i * NODE_PER_BLOCK + j] 
                    == self.block_perms@[self.block_ptrs@[i] as int].view().value.get_Some_0()@[j]));
        }
}


}