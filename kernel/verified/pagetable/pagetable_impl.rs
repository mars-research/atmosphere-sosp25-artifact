use vstd::prelude::*;
use vstd::ptr::*;
use crate::define::*;
use crate::page_alloc::*;

use crate::pagetable::*;
use vstd::set_lib::lemma_set_properties;

verus!{
impl PageTable{

    pub fn map(&mut self, va:VAddr, dst:PAddr) -> (ret: bool)
        requires 
            old(self).wf(),
            spec_va_valid(va),
            //old(self).is_va_entry_exist(va),
            old(self).get_pagetable_page_closure().contains(dst) == false,
            old(self).mapping@[va] == 0,
        ensures
            self.wf(),
            old(self).is_va_entry_exist(va) == ret ,
            old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,dst),
            !old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@,
    {
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_ptr = *l4_tbl.table.get(l4i);
        if(l3_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }
        assert(self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_ptr = *l3_tbl.table.get(l3i);
        if(l2_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }

        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l3_tables@[l3_ptr]@.value.get_Some_0().table@.contains(l2_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_ptr = *l2_tbl.table.get(l2i);
        if(l1_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }
        assert(self.is_va_entry_exist(va));
        assert(old(self).is_va_entry_exist(va));

        assert(self.l2_tables@.dom().contains(l2_ptr));
        assert(self.l2_tables@[l2_ptr]@.value.get_Some_0().table@.contains(l1_ptr));
        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<LookUpTable>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().table.wf());
        //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

        LookUpTable_set(&l1_pptr,Tracked(&mut l1_perm),l1i,dst);
        assert(l1_perm@.value.get_Some_0().table@[l1i as int] == dst);
        assert(l1_perm@.pptr == l1_ptr);
        proof {
            self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),dst);}
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);

        proof {
            self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);

        }

        assert(self.wf_l4());
        
        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        proof{
            self.wf_to_wf_mapping();
            pagetable_virtual_mem_lemma();    
        }

        assert(self.no_self_mapping());


        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == dst);

        let g_va:Ghost<usize> = Ghost(spec_index2va((l4i,l3i,l2i,l1i)));
        assert(forall|va:usize| #![auto] spec_va_valid(va) && va != g_va ==> 
            self.mapping@[va] == old(self).mapping@[va]);

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
                self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) == l1_ptr && _l1i != l1i==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && ((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );
        assert(self.wf_mapping());

        assert(self.wf());

        //  assert(false);

        return true;

    }
    pub fn unmap(&mut self, va:VAddr) -> (ret: PAddr)
        requires 
            old(self).wf(),
            spec_va_valid(va),
            // old(self).mapping@[va] != 0,
        ensures
            self.wf(),
            old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,0),
            !old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@,
            old(self).mapping@[va] != 0 ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,0),
            old(self).mapping@[va] == 0 ==> 
                self.mapping@ =~= old(self).mapping@,
            ret == old(self).mapping@[va],
    {
        proof{
            pagetable_virtual_mem_lemma();    
        }
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_ptr = *l4_tbl.table.get(l4i);
        if(l3_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return 0;
        }
        assert(self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_ptr = *l3_tbl.table.get(l3i);
        if(l2_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return 0;
        }

        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l3_tables@[l3_ptr]@.value.get_Some_0().table@.contains(l2_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_ptr = *l2_tbl.table.get(l2i);
        if(l1_ptr == 0){
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return 0;
        }
        assert(self.is_va_entry_exist(va));
        assert(old(self).is_va_entry_exist(va));

        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l1_ptr).borrow(Tracked(l1_perm));
        let dst = *l1_tbl.table.get(l1i);

        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==dst);
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);
        assert(self.mapping@[va]==dst);
        
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<LookUpTable>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().table.wf());
        //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

        LookUpTable_set(&l1_pptr,Tracked(&mut l1_perm),l1i,0);
        assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);
        assert(l1_perm@.pptr == l1_ptr);
        proof {
            self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),0);}
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);

        proof {
            self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);

        }

        assert(self.wf_l4());
        
        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        proof{
            self.wf_to_wf_mapping();
        }

        assert(self.no_self_mapping());


        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == 0);

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
            self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) == l1_ptr && _l1i != l1i==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && ((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(self.wf_mapping());

        assert(self.wf());
        // assert(false);

        return dst;
    }
    pub fn get_va_entry(&self, va:VAddr) -> (ret:Option<PAddr>)
        requires
            self.wf(),
            spec_va_valid(va),
        ensures
            self.is_va_entry_exist(va) == ret.is_Some(),
            self.is_va_entry_exist(va) ==> self.mapping@[va] == ret.unwrap(),
    {
        proof{
            pagetable_virtual_mem_lemma();    
        }
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_ptr = *l4_tbl.table.get(l4i);
        if(l3_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return None;
        }
        assert(self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_ptr = *l3_tbl.table.get(l3i);
        if(l2_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return None;
        }

        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l3_tables@[l3_ptr]@.value.get_Some_0().table@.contains(l2_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_ptr = *l2_tbl.table.get(l2i);
        if(l1_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==0);
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==0);
            assert(self.mapping@[va]==0);
            return None;
        }
        assert(self.is_va_entry_exist(va));

        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l1_ptr).borrow(Tracked(l1_perm));
        let dst = *l1_tbl.table.get(l1i);

        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==dst);
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);
        assert(self.mapping@[va]==dst);

        return Some(dst);
    }

    pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
            spec_va_valid(va),
            old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self).get_pagetable_get_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self.mapping@ =~= old(self).mapping@,
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
            self.is_va_entry_exist(va),
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
    {
        let mut ret:Ghost<Set<PagePtr>> = Ghost(Set::empty());
        proof{
            pagetable_virtual_mem_lemma();  
            lemma_set_properties::<Set<PagePtr>>();  
        }
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(l4i >= KERNEL_MEM_END_L4INDEX);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let mut l3_ptr = *l4_tbl.table.get(l4i);
        if(l3_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l3 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l3_tables@.dom().contains(page_ptr) == false);

            assert(self.l4_table@.dom().contains(self.cr3));
            let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
            assert(self.cr3 == l4_perm@.pptr);
            let l4_pptr = PPtr::<LookUpTable>::from_usize(self.cr3);

            assert(l4_perm@.value.get_Some_0().table.wf());
            //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

            LookUpTable_set(&l4_pptr,Tracked(&mut l4_perm),l4i,page_ptr);
            assert(l4_perm@.value.get_Some_0().table@[l4i as int] == page_ptr);
            assert(l4_perm@.pptr == self.cr3);
    
            proof {
                self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            }
            let (l3_ptr_tmp,mut l3_perm) = page_to_lookuptable((page_ptr,page_perm));
            proof{
                self.l3_tables.borrow_mut().tracked_insert(l3_ptr_tmp, l3_perm.get());
            }
            assert(self.wf_l4());
        
            assert(self.wf_l3());
            
            assert(self.wf_l2());

            assert(self.wf_l1());

            proof{
                self.wf_to_wf_mapping();
            }

            assert(self.no_self_mapping());

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j != l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j == l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());
            l3_ptr = l3_ptr_tmp;
            proof{ret@ = ret@.insert(l3_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
            assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }
        assert(self.wf());
        assert(self.resolve_mapping_l4(l4i) == l3_ptr);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
        assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

        assert(self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let mut l2_ptr = *l3_tbl.table.get(l3i);
        if(l2_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l2 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l3_tables@.dom().contains(page_ptr) == false);

            assert(self.l3_tables@.dom().contains(l3_ptr));
            let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(l3_ptr);
            assert(l3_ptr == l3_perm@.pptr);
            let l3_pptr = PPtr::<LookUpTable>::from_usize(l3_ptr);

            assert(l3_perm@.value.get_Some_0().table.wf());
            //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

            LookUpTable_set(&l3_pptr,Tracked(&mut l3_perm),l3i,page_ptr);
            assert(l3_perm@.value.get_Some_0().table@[l3i as int] == page_ptr);
            assert(l3_perm@.pptr == l3_ptr);
    
            proof {
                self.l3_tables.borrow_mut().tracked_insert(l3_ptr, l3_perm);
            }
            let (l2_ptr_tmp,mut l2_perm) = page_to_lookuptable((page_ptr,page_perm));
            proof{
                self.l2_tables.borrow_mut().tracked_insert(l2_ptr_tmp, l2_perm.get());
            }
            assert(self.wf_l4());
        
            assert(self.wf_l3());
            
            assert(self.wf_l2());

            assert(self.wf_l1());

            proof{
                self.wf_to_wf_mapping();
            }

            assert(self.no_self_mapping());

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l3j != l3i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l3j == l3i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());

            l2_ptr = l2_ptr_tmp;
            proof{ret@ = ret@.insert(l2_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
            assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }
        assert(self.wf());
        assert(self.resolve_mapping_l3(l4i,l3i) == l2_ptr);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
        assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let mut l1_ptr = *l2_tbl.table.get(l2i);
        if(l1_ptr == 0){
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l2 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l2_tables@.dom().contains(page_ptr) == false);

            assert(self.l2_tables@.dom().contains(l2_ptr));
            let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(l2_ptr);
            assert(l2_ptr == l2_perm@.pptr);
            let l2_pptr = PPtr::<LookUpTable>::from_usize(l2_ptr);

            assert(l2_perm@.value.get_Some_0().table.wf());
            //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

            LookUpTable_set(&l2_pptr,Tracked(&mut l2_perm),l2i,page_ptr);
            assert(l2_perm@.value.get_Some_0().table@[l2i as int] == page_ptr);
            assert(l2_perm@.pptr == l2_ptr);
    
            proof {
                self.l2_tables.borrow_mut().tracked_insert(l2_ptr, l2_perm);
            }
            let (l1_ptr_tmp,mut l1_perm) = page_to_lookuptable((page_ptr,page_perm));
            proof{
                self.l1_tables.borrow_mut().tracked_insert(l1_ptr_tmp, l1_perm.get());
            }
            assert(self.wf_l4());
        
            assert(self.wf_l3());
            
            assert(self.wf_l2());

            assert(self.wf_l1());

            proof{
                self.wf_to_wf_mapping();
            }

            assert(self.no_self_mapping());

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j != l2i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j == l2i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());

            l1_ptr = l1_ptr_tmp;
            proof{ret@ = ret@.insert(l1_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
            assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }
        assert(self.wf());
        assert(self.resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
        assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

        assert(self.mapping@ =~= old(self).mapping@);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
        assert(self.is_va_entry_exist(va));

        assert(page_alloc.wf());
        assert(page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages());
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
        assert(page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@);
        return ret;
    }


    pub fn unmap_page_no_lookup(&mut self,page_alloc :&mut PageAllocator, l4i:usize, l3i:usize, l2i:usize, l1i:usize,  l3_ptr:usize, l2_ptr:usize, l1_ptr:usize)
        requires
            old(self).wf(),
            KERNEL_MEM_END_L4INDEX <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
            old(self).l4_entry_exists(l4i),
            old(self).l3_entry_exists(l4i,l3i),
            old(self).l2_entry_exists(l4i,l3i,l2i),
            old(self).resolve_mapping_l4(l4i) == l3_ptr,
            old(self).resolve_mapping_l3(l4i,l3i) == l2_ptr,
            old(self).resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr,
            old(self).resolve_mapping_l2(l4i,l3i,l2i) != 0,
        ensures
            self.wf(),
            self.l4_entry_exists(l4i),
            self.l3_entry_exists(l4i,l3i),
            self.l2_entry_exists(l4i,l3i,l2i),
            self.resolve_mapping_l4(l4i) == l3_ptr,
            self.resolve_mapping_l3(l4i,l3i) == l2_ptr,
            self.resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr,
            self.resolve_mapping_l2(l4i,l3i,l2i) != 0,
            forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
                self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))],
            self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))] == 0,
            forall|j:usize| 0<=j<512 && j != l1i ==> 
                self.l1_tables@[l1_ptr]@.value.get_Some_0().table@[j as int] == old(self).l1_tables@[l1_ptr]@.value.get_Some_0().table@[j as int],
            self.l1_tables@[l1_ptr]@.value.get_Some_0().table@[l1i as int] == 0,

    {
        proof{
            pagetable_virtual_mem_lemma();
        }
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<LookUpTable>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().table.wf());
        assert(l1_perm@.pptr == l1_ptr);
        LookUpTable_set(&l1_pptr,Tracked(&mut l1_perm),l1i,0);
        proof {self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),0);}

        proof {self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);}

        assert(self.wf_l4());

        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        proof{
            self.wf_to_wf_mapping();
        }

        assert(self.no_self_mapping());

        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == 0);

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
            self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) == l1_ptr && _l1i != l1i==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && _l1i != l1i ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(self.wf_mapping());

        assert(self.wf());
    }

}

}