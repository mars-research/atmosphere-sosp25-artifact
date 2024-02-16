use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;
use vstd::ptr::PointsTo;
use vstd::ptr::PPtr;
use core::mem::MaybeUninit;

use crate::pagetable::*;
use crate::page_alloc::*;



pub open spec fn va_perm_bits_valid(perm:usize) -> bool{
    (perm ^ VA_PERM_MASK as usize) == 0
}

// #[verifier(external_body)]
// pub fn LookUpTable_set(pptr:&PPtr<LookUpTable>, Tracked(perm): Tracked<&mut PointsTo<LookUpTable>>, i: usize, value:usize) 
//     requires 
//         pptr.id() == old(perm)@.pptr,
//         old(perm)@.value.is_Some(),
//         old(perm)@.value.get_Some_0().table.wf(),
//         0<=i<512,
//     ensures
//         pptr.id() == perm@.pptr,
//         perm@.value.is_Some(),
//         perm@.value.get_Some_0().table.wf(),
//         forall|j:usize| 0<=j<512 && j != i ==> 
//             perm@.value.get_Some_0().table@[j as int] == old(perm)@.value.get_Some_0().table@[j as int],
//         perm@.value.get_Some_0().table@[i as int] == value,
// {
//     unsafe {
//         let uptr = pptr.to_usize() as *mut MaybeUninit<LookUpTable>;
//         (*uptr).assume_init_mut().table.set(i,value);
//     }
// }


// #[verifier(external_body)]
// pub fn page_to_lookuptable(page: (PagePtr,Tracked<PagePerm>)) -> (ret :(PagePtr, Tracked<PointsTo<LookUpTable>>))
//     requires page.0 == page.1@@.pptr,
//             page.1@@.value.is_Some(),
//     ensures ret.0 == ret.1@@.pptr,
//             ret.0 == page.0,
//             ret.1@@.value.is_Some(),
//             ret.1@@.value.get_Some_0().table.wf(),
//             forall|i:usize| 0<=i<512 ==> ret.1@@.value.get_Some_0().table@[i as int] == 0,

// {
//     (page.0, Tracked::assume_new())
// }

#[verifier(external_body)]
pub fn pagemap_set(pptr:&PPtr<PageMap>, Tracked(perm): Tracked<&mut PointsTo<PageMap>>, i: usize, value:Option<PageEntry>) 
    requires 
        pptr.id() == old(perm)@.pptr,
        old(perm)@.value.is_Some(),
        old(perm)@.value.get_Some_0().wf(),
        0<=i<512,
        value.is_Some() ==> page_ptr_valid(value.unwrap().addr),
        value.is_Some() ==> va_perm_bits_valid(value.unwrap().perm),
    ensures
        pptr.id() == perm@.pptr,
        perm@.value.is_Some(),
        perm@.value.get_Some_0().wf(),
        forall|j:usize| 0<=j<512 && j != i ==> 
            perm@.value.get_Some_0()[j] =~= old(perm)@.value.get_Some_0()[j],
        perm@.value.get_Some_0()[i] =~= value,
        value.is_Some() ==> perm@.value.get_Some_0()[i].get_Some_0().addr =~= value.get_Some_0().addr,
        value.is_Some() ==> perm@.value.get_Some_0()[i].get_Some_0().perm =~= value.get_Some_0().perm,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(i,value);
    }
}

#[verifier(external_body)]
pub fn page_to_pagemap(page: (PagePtr,Tracked<PagePerm>)) -> (ret :(PagePtr, Tracked<PointsTo<PageMap>>))
    requires page.0 == page.1@@.pptr,
            page.1@@.value.is_Some(),
    ensures ret.0 == ret.1@@.pptr,
            ret.0 == page.0,
            ret.1@@.value.is_Some(),
            ret.1@@.value.get_Some_0().wf(),
            forall|i:usize| 0<=i<512 ==> ret.1@@.value.get_Some_0()[i].is_None(),

{
    (page.0, Tracked::assume_new())
}

pub open spec fn spec_va_valid(va: usize) -> bool
{
    (va & VA_MASK as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64) >= KERNEL_MEM_END_L4INDEX
}

pub open spec fn spec_v2l1index(va: usize) -> L1Index
{
    (va >> 12 & 0x1ff) as usize
}

pub open spec fn spec_v2l2index(va: usize) -> L2Index
{
    (va >> 21 & 0x1ff) as usize
}

pub open spec fn spec_v2l3index(va: usize) -> L3Index
{
    (va >> 30 & 0x1ff) as usize
}

pub open spec fn spec_v2l4index(va: usize) -> L4Index
{
    (va >> 39 & 0x1ff) as usize
}

pub open spec fn spec_va2index(va: usize) -> (L4Index,L3Index,L2Index,L1Index)
{
    (spec_v2l4index(va),spec_v2l3index(va),spec_v2l2index(va),spec_v2l1index(va))
}

pub open spec fn spec_index2va(i:(L4Index,L3Index,L2Index,L1Index)) -> usize
    recommends 
    i.0 <= 0x1ff,
    i.1 <= 0x1ff, 
    i.2 <= 0x1ff,
    i.3 <= 0x1ff,           
{
    (i.0 as usize)<<39 & (i.1 as usize)<<30 & (i.2 as usize)<<21 & (i.3 as usize)<<12 
} 


pub fn va_valid(va: usize) -> (ret: bool)
    ensures ret == spec_va_valid(va),
{
    (va & VA_MASK as usize == 0) &&  (va as u64 >> 39u64 & 0x1ffu64) >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(external_body)]
pub fn v2l1index(va: usize) -> (ret: L1Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l1index(va),
             ret <= 0x1ff,
{
    (va as u64 >> 12u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l2index(va: usize) -> (ret: L2Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l2index(va),
            ret <= 0x1ff,
{
    (va as u64 >> 21u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l3index(va: usize) -> (ret: L3Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l3index(va),
            ret <= 0x1ff,
{
    (va as u64 >> 30u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l4index(va: usize) -> (ret: L4Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l4index(va),
            KERNEL_MEM_END_L4INDEX <= ret <= 0x1ff,
{
    (va as u64 >> 39u64 & 0x1ffu64) as usize
}


pub fn va2index(va: usize) -> (ret : (L4Index,L3Index,L2Index,L1Index))
    requires
        spec_va_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret.3 == spec_v2l1index(va) && ret.3 <= 0x1ff,
{
    (v2l4index(va),v2l3index(va),v2l2index(va),v2l1index(va))
}


#[verifier(external_body)]
pub proof fn pagetable_virtual_mem_lemma()
    ensures
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize|  #![auto] (
            KERNEL_MEM_END_L4INDEX <= l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff 
            ) ==>
                spec_va_valid(spec_index2va((l4i,l3i,l2i,l1i)))
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).0 == l4i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).1 == l3i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).2 == l2i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).3 == l1i
        ),
        (forall|va_1:usize| #![auto] spec_va_valid(va_1) ==> (
            KERNEL_MEM_END_L4INDEX <= spec_va2index(va_1).0 <= 0x1ff
            &&
            spec_va2index(va_1).1 <= 0x1ff
            &&
            spec_va2index(va_1).2 <= 0x1ff
            &&
            spec_va2index(va_1).3 <= 0x1ff
            &&
            spec_index2va(spec_va2index(va_1)) == va_1
        )),
        (forall|va_1:usize, va_2:usize| #![auto] spec_va_valid(va_1) && spec_va_valid(va_2) && va_1 == va_2 ==> (
            spec_va2index(va_1).0 == spec_va2index(va_2).0 
            &&
            spec_va2index(va_1).1 == spec_va2index(va_2).1  
            &&
            spec_va2index(va_1).2 == spec_va2index(va_2).2 
            &&
            spec_va2index(va_1).3 == spec_va2index(va_2).3
        )),
        (forall|va_1:usize, va_2:usize| #![auto] spec_va_valid(va_1) && spec_va_valid(va_2) && va_1 != va_2 ==> (
            spec_va2index(va_1).0 != spec_va2index(va_2).0 
            ||
            spec_va2index(va_1).1 != spec_va2index(va_2).1  
            ||
            spec_va2index(va_1).2 != spec_va2index(va_2).2 
            ||
            spec_va2index(va_1).3 != spec_va2index(va_2).3
        )),
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize,l4j: usize, l3j: usize, l2j: usize, l1j: usize|  #![auto] (
            KERNEL_MEM_END_L4INDEX <= l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff && l4j <= 0x1ff && l3j <= 0x1ff && l2j <= 0x1ff && l1j <= 0x1ff &&
            l4i == l4j && l3i == l3j && l2i == l2j && l1i == l1j  
        ) ==>
            spec_index2va((l4i,l3i,l2i,l1i)) == spec_index2va((l4j,l3j,l2j,l1j))
        ),
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize,l4j: usize, l3j: usize, l2j: usize, l1j: usize|  #![auto] (
            KERNEL_MEM_END_L4INDEX <= l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff && l4j <= 0x1ff && l3j <= 0x1ff && l2j <= 0x1ff && l1j <= 0x1ff &&
            l4i != l4j || l3i != l3j || l2i != l2j || l1i != l1j  
        ) ==>
            spec_index2va((l4i,l3i,l2i,l1i)) != spec_index2va((l4j,l3j,l2j,l1j))
        )
        
{

}

#[verifier(external_body)]
pub proof fn pagemap_permission_bits_lemma()
    ensures
        (0usize & (PAGE_ENTRY_PRESENT_MASK as usize) == 0),
        (forall|i:usize| #![auto] (i | (PAGE_ENTRY_PRESENT_MASK as usize)) & (PAGE_ENTRY_PRESENT_MASK as usize) == 1),
        (forall|i:usize| #![auto] page_ptr_valid(i) ==> 
            ((i | (PAGE_ENTRY_PRESENT_MASK as usize)) & (VA_MASK as usize)) == i),
        (forall|i:usize, j:usize| #![auto] page_ptr_valid(i) && va_perm_bits_valid(j) ==>
            (
                ((((i | j) | (PAGE_ENTRY_PRESENT_MASK as usize)) & (VA_MASK as usize)) == i)
            )
        ),
        (forall|i:usize, j:usize| #![auto] page_ptr_valid(i) && va_perm_bits_valid(j) ==>
            (
                ((((i | j) | (PAGE_ENTRY_PRESENT_MASK as usize)) & (VA_PERM_MASK as usize)) == j)
            )
        ),
        (forall|i:usize, j:usize| #![auto] page_ptr_valid(i) && va_perm_bits_valid(j) ==>
            (
                (((i | j)  & (VA_MASK as usize)) == i)
            )
        ),
        (forall|i:usize, j:usize| #![auto] page_ptr_valid(i) && va_perm_bits_valid(j) ==>
            (
                (((i | j)  & (VA_PERM_MASK as usize)) == j)
            )
        ),
        va_perm_bits_valid(0usize) == true,
    {

    }

}