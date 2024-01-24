use vstd::prelude::*;
use crate::define::*;
use crate::page_alloc::*;

verus! {
#[verifier(external_body)]
pub proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    unimplemented!();
}

#[verifier(external_body)]
pub proof fn lemma_usize_int(x: int)
    ensures
        x as usize as int == x,
{
    unimplemented!();
}

//TODO: @Xiangdong prove this
#[verifier(external_body)]
pub proof fn page_ptr_lemma()
    ensures 
        forall|ptr:PagePtr| #![auto] page_ptr_valid(ptr) ==> page_index_valid(page_ptr2page_index(ptr)),
        forall|index:usize| #![auto] page_index_valid(index) ==> page_ptr_valid(page_index2page_ptr(index)),
        forall|ptr:PagePtr| #![auto] page_ptr_valid(ptr) ==> page_index2page_ptr(page_ptr2page_index(ptr)) == ptr,
        forall|index:usize| #![auto] page_index_valid(index) ==> page_ptr2page_index(page_index2page_ptr(index)) == index,
{
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> (index * 4096) % 4096 == 0);
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> (index * 4096) == page_index2page_ptr(index));
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> page_index2page_ptr(index) % 4096 == 0);
}
}