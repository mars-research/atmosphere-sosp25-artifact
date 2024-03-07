
use vstd::prelude::*;
verus!{


use vstd::ptr::*;
use crate::define::*;
use crate::page_alloc::*;
use crate::pagetable::*;
// use vstd::set_lib::*;
    
impl PageTable{

    pub fn map(&mut self, va:VAddr, dst:PageEntry) -> (ret: bool)
        requires 
            old(self).wf(),
            spec_va_valid(va),
            //old(self).is_va_entry_exist(va),
            old(self).get_pagetable_page_closure().contains(dst.addr) == false,
            old(self).mapping@[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
        ensures
            self.wf(),
            old(self).is_va_entry_exist(va) == ret ,
            old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,Some(dst)),
            !old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@,
    {
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_option = l4_tbl.get(l4i);
        if l3_option.is_none(){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }else{
            assert(l3_option.is_Some());
            // assert(false);
        }
        let l3_ptr = l3_option.unwrap().addr;
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &PageMap = PPtr::<PageMap>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_option = l3_tbl.get(l3i);
        if l2_option.is_none(){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }
        let l2_ptr = l2_option.unwrap().addr;
        assert(self.l3_tables@.dom().contains(l3_ptr));
        // assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &PageMap = PPtr::<PageMap>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_option = l2_tbl.get(l2i);
        if l1_option.is_none(){
            assert(!old(self).is_va_entry_exist(va));
            return false;
        }
        let l1_ptr = l1_option.unwrap().addr;
        assert(self.is_va_entry_exist(va));
        assert(old(self).is_va_entry_exist(va));

        assert(self.l2_tables@.dom().contains(l2_ptr));
        // assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<PageMap>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().wf());
        //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);
        pagemap_set(&l1_pptr,Tracked(&mut l1_perm),l1i,Some(dst));
        assert(l1_perm@.value.get_Some_0()[l1i] =~= Some(dst));
        assert(l1_perm@.pptr == l1_ptr);
        proof {
            self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),Some(dst));}
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]=~= Some(dst));

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


        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) =~= Some(dst));

        let g_va:Ghost<usize> = Ghost(spec_index2va((l4i,l3i,l2i,l1i)));
        assert(forall|va:usize| #![auto] spec_va_valid(va) && va != g_va ==> 
            self.mapping@[va] =~= old(self).mapping@[va]);

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
                self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] =~= old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && 
            self.resolve_mapping_l2(_l4i,_l3i,_l2i).is_Some() && self.resolve_mapping_l2(_l4i,_l3i,_l2i).unwrap().addr != l1_ptr ==> 
            (
                self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i)
            )
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && 
            self.resolve_mapping_l2(_l4i,_l3i,_l2i).is_Some() && self.resolve_mapping_l2(_l4i,_l3i,_l2i).unwrap().addr == l1_ptr && _l1i != l1i ==> 
            (
                self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i)
            )
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

    pub fn unmap(&mut self, va:VAddr) -> (ret: Option<PageEntry>)
        requires 
            old(self).wf(),
            spec_va_valid(va),
            // old(self).mapping@[va] != 0,
        ensures
            self.wf(),
            old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,None),
            !old(self).is_va_entry_exist(va) ==> 
                self.mapping@ =~= old(self).mapping@,
            old(self).mapping@[va].is_Some() ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,None),
            old(self).mapping@[va].is_None() ==> 
                self.mapping@ =~= old(self).mapping@,
            ret == old(self).mapping@[va],
    {
        proof{
            pagetable_virtual_mem_lemma();    
        }
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_option = l4_tbl.get(l4i);
        if l3_option.is_none() {
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l3_ptr = l3_option.unwrap().addr;
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &PageMap = PPtr::<PageMap>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_option = l3_tbl.get(l3i);
        if l2_option.is_none() {
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l2_ptr = l2_option.unwrap().addr;
        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &PageMap = PPtr::<PageMap>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_option = l2_tbl.get(l2i);
        if l1_option.is_none() {
            assert(!old(self).is_va_entry_exist(va));
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l1_ptr = l1_option.unwrap().addr;
        assert(self.is_va_entry_exist(va));
        assert(old(self).is_va_entry_exist(va));

        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_tbl : &PageMap = PPtr::<PageMap>::from_usize(l1_ptr).borrow(Tracked(l1_perm));
        let dst = l1_tbl.get(l1i);

        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==dst);
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);
        assert(self.mapping@[va]==dst);
        
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<PageMap>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().wf());

        pagemap_set(&l1_pptr,Tracked(&mut l1_perm),l1i,None);
        assert(l1_perm@.value.get_Some_0()[l1i].is_None());
        assert(l1_perm@.pptr == l1_ptr);
        proof {
            self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),None);}
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());

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


        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
            (
                self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]
            )
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i).get_Some_0().addr != l1_ptr ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i).get_Some_0().addr  == l1_ptr && _l1i != l1i==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 
            0<= _l2i < 512  && 0<= _l1i < 512  && ((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(self.wf_mapping());

        assert(self.wf());
        // assert(false);

        return dst;
    }


    pub fn get_va_entry(&self, va:VAddr) -> (ret:Option<PageEntry>)
        requires
            self.wf(),
            spec_va_valid(va),
        ensures
            self.mapping@[va] == ret,
    {
        proof{
            pagetable_virtual_mem_lemma();    
        }
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_option = l4_tbl.get(l4i);
        if l3_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l3_ptr = l3_option.unwrap().addr;
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &PageMap = PPtr::<PageMap>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_option = l3_tbl.get(l3i);
        if l2_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l2_ptr = l2_option.unwrap().addr;
        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &PageMap = PPtr::<PageMap>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_option = l2_tbl.get(l2i);
        if l1_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i).is_None());
            assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))].is_None());
            assert(self.mapping@[va].is_None());
            return None;
        }
        let l1_ptr = l1_option.unwrap().addr;
        assert(self.is_va_entry_exist(va));

        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_tbl : &PageMap = PPtr::<PageMap>::from_usize(l1_ptr).borrow(Tracked(l1_perm));
        let dst = l1_tbl.get(l1i);

        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i)==dst);
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);
        assert(self.mapping@[va]==dst);

        return dst;
    }

    pub fn create_va_entry_l3(&mut self, va:VAddr,page_alloc :&mut PageAllocator, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> (ret:(PAddr,Ghost<Set<PagePtr>>))
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
            (l4i,l3i,l2i,l1i) =~= spec_va2index(va),
        ensures
            self.wf(),
            self.get_pagetable_mapped_pages() =~= old(self).get_pagetable_mapped_pages(),
            self.get_pagetable_mapped_pages().disjoint(page_alloc.get_free_pages_as_set()),
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
            ret.1@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self.mapping@ =~= old(self).mapping@,
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
            self.resolve_mapping_l4(l4i).is_Some(),
            self.resolve_mapping_l4(l4i).get_Some_0().addr =~= ret.0,
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret.1@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            page_alloc.free_pages.len() >= 2,
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 1,
            self.get_pagetable_mapped_pages().disjoint(page_alloc.get_free_pages_as_set()),
    {
        let mut ret_set:Ghost<Set<PagePtr>> = Ghost(Set::empty());
        proof{
            pagetable_virtual_mem_lemma();  
            page_ptr_lemma();
            pagemap_permission_bits_lemma();
            // lemma_set_properties::<Set<PagePtr>>();  
        }
        assert(l4i >= KERNEL_MEM_END_L4INDEX);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let mut l3_option = l4_tbl.get(l4i);
        let mut l3_ptr = 0;
        if l3_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l3 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l3_tables@.dom().contains(page_ptr) == false);
            assert(self.cr3 != page_ptr);

            assert(self.l4_table@.dom().contains(self.cr3));
            let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
            assert(self.cr3 == l4_perm@.pptr);
            let l4_pptr = PPtr::<PageMap>::from_usize(self.cr3);

            assert(l4_perm@.value.get_Some_0().wf());
            //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

            l3_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});


            pagemap_set(&l4_pptr,Tracked(&mut l4_perm),l4i,l3_option);

            assert(l4_perm@.value.get_Some_0()[l4i] == l3_option);
            assert(l4_perm@.pptr == self.cr3);
    
            proof {
                self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            }
            assert(self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().addr == page_ptr);
            
            let (l3_ptr_tmp,mut l3_perm) = page_to_pagemap((page_ptr,page_perm));
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

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j != l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j == l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());
            l3_ptr = l3_ptr_tmp;
            proof{ret_set@ = ret_set@.insert(l3_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
            assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }else{
            l3_ptr = l3_option.unwrap().addr;
        }
        assert(self.wf());
        assert(self.resolve_mapping_l4(l4i) == l3_option);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
        assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        
        return (l3_ptr,ret_set);
    }

    pub fn create_va_entry_l2(&mut self, va:VAddr,page_alloc :&mut PageAllocator, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index, l3_ptr: PAddr) -> (ret:(PAddr,Ghost<Set<PagePtr>>))
    requires
        old(self).wf(),
        old(page_alloc).wf(),
        old(page_alloc).free_pages.len() >=2,
        spec_va_valid(va),
        (l4i,l3i,l2i,l1i) =~= spec_va2index(va),
        old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
        old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        old(self).resolve_mapping_l4(l4i).is_Some(),
        old(self).resolve_mapping_l4(l4i).get_Some_0().addr == l3_ptr,
    ensures
        self.wf(),
        self.get_pagetable_mapped_pages() =~= old(self).get_pagetable_mapped_pages(),
        self.get_pagetable_mapped_pages().disjoint(page_alloc.get_free_pages_as_set()),
        self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
        page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
        ret.1@.subset_of(old(page_alloc).get_free_pages_as_set()),
        self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
        self.mapping@ =~= old(self).mapping@,
        self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
        self.resolve_mapping_l3(l4i,l3i).is_Some(),
        self.resolve_mapping_l3(l4i,l3i).get_Some_0().addr =~= ret.0,
        page_alloc.wf(),
        page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
        page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
        page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret.1@,
        page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
        forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
        forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
        page_alloc.free_pages.len() >= 1,
        page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 1,
{
    proof{
        pagetable_virtual_mem_lemma();  
        page_ptr_lemma();
        pagemap_permission_bits_lemma();
        // lemma_set_properties::<Set<PagePtr>>();  
    }
    let mut ret_set:Ghost<Set<PagePtr>> = Ghost(Set::empty());
    let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &PageMap = PPtr::<PageMap>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let mut l2_option = l3_tbl.get(l3i);
        let mut l2_ptr:PAddr = 0;
        if l2_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l2 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l3_tables@.dom().contains(page_ptr) == false);

            assert(self.l3_tables@.dom().contains(l3_ptr));
            let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(l3_ptr);
            assert(l3_ptr == l3_perm@.pptr);
            let l3_pptr = PPtr::<PageMap>::from_usize(l3_ptr);

            assert(l3_perm@.value.get_Some_0().wf());
            //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

            l2_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});
            pagemap_set(&l3_pptr,Tracked(&mut l3_perm),l3i,l2_option);
            assert(l3_perm@.value.get_Some_0()[l3i] == l2_option);
            assert(l3_perm@.pptr == l3_ptr);
    
            proof {
                self.l3_tables.borrow_mut().tracked_insert(l3_ptr, l3_perm);
            }
            assert(self.l3_tables@[l3_ptr]@.value.get_Some_0()[l3i].get_Some_0().addr == page_ptr);
            let (l2_ptr_tmp,mut l2_perm) = page_to_pagemap((page_ptr,page_perm));
            proof{
                self.l2_tables.borrow_mut().tracked_insert(l2_ptr_tmp, l2_perm.get());
            }
            assert(self.wf_l4());
        
            assert(self.wf_l3());

            assert(self.wf_l2());

            assert(self.wf_l1());

            assert(self.no_self_mapping());

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j != l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j == l4i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());

            l2_ptr = l2_ptr_tmp;
            proof{ret_set@ = ret_set@.insert(l2_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
            assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }else{
            l2_ptr = l2_option.unwrap().addr;
        }
        assert(self.wf());
        assert(self.resolve_mapping_l3(l4i,l3i).is_Some());
        assert(self.resolve_mapping_l3(l4i,l3i).get_Some_0().addr == l2_ptr);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
        assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
    
    return (l2_ptr,ret_set);
}

pub fn create_va_entry_l1(&mut self, va:VAddr,page_alloc :&mut PageAllocator, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index, l2_ptr: PAddr) -> (ret:(PAddr, Ghost<Set<PagePtr>>))
requires
    old(self).wf(),
    old(page_alloc).wf(),
    old(page_alloc).free_pages.len() >=1,
    spec_va_valid(va),
    (l4i,l3i,l2i,l1i) =~= spec_va2index(va),
    old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
    old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
    old(self).resolve_mapping_l3(spec_va2index(va).0,spec_va2index(va).1).is_Some(),
    old(self).resolve_mapping_l3(spec_va2index(va).0,spec_va2index(va).1).get_Some_0().addr == l2_ptr,
ensures
    self.wf(),
    self.get_pagetable_mapped_pages() =~= old(self).get_pagetable_mapped_pages(),
    self.get_pagetable_mapped_pages().disjoint(page_alloc.get_free_pages_as_set()),
    self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
    page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
    ret.1@.subset_of(old(page_alloc).get_free_pages_as_set()),
    self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
    self.mapping@ =~= old(self).mapping@,
    self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret.1@,
    self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
    self.resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr =~= ret.0,
    page_alloc.wf(),
    page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
    page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret.1@,
    page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret.1@,
    page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
    forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
    forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
    page_alloc.free_pages.len() >= 0,
    page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 1,
{
proof{
    pagetable_virtual_mem_lemma();  
    page_ptr_lemma();
    pagemap_permission_bits_lemma();
    // lemma_set_properties::<Set<PagePtr>>();  
}
    let mut ret_set:Ghost<Set<PagePtr>> = Ghost(Set::empty());
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &PageMap = PPtr::<PageMap>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let mut l1_option = l2_tbl.get(l2i);
        let mut l1_ptr:usize = 0;
        if l1_option.is_none() {
            assert(self.is_va_entry_exist(va) == false);
            //alloc new page for l2 page
            let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
            assume(page_ptr != 0);
            assert(self.l2_tables@.dom().contains(page_ptr) == false);

            assert(self.l2_tables@.dom().contains(l2_ptr));
            let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(l2_ptr);
            assert(l2_ptr == l2_perm@.pptr);
            let l2_pptr = PPtr::<PageMap>::from_usize(l2_ptr);

            assert(l2_perm@.value.get_Some_0().wf());
            //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

            l1_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});
            pagemap_set(&l2_pptr,Tracked(&mut l2_perm),l2i,l1_option);
            assert(l2_perm@.value.get_Some_0()[l2i] == l1_option);
            assert(l2_perm@.pptr == l2_ptr);
    
            proof {
                self.l2_tables.borrow_mut().tracked_insert(l2_ptr, l2_perm);
            }
            let (l1_ptr_tmp,mut l1_perm) = page_to_pagemap((page_ptr,page_perm));
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

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j != l2i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j == l2i) 
                ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

            assert(self.wf_mapping());
            assert(self.wf());

            l1_ptr = l1_ptr_tmp;
            proof{ret_set@ = ret_set@.insert(l1_ptr_tmp);}
            assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
            assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
            assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
            assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
        }else{
            l1_ptr = l1_option.unwrap().addr;
        }
        assert(self.wf());
        assert(self.resolve_mapping_l2(l4i,l3i,l2i).is_Some());
        assert(self.resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr == l1_ptr);
        assert(self.resolve_mapping_l2(l4i,l3i,l2i) =~= l1_option);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
        assert(ret_set@.subset_of(old(page_alloc).get_free_pages_as_set()));
        assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

        assert(self.mapping@ =~= old(self).mapping@);
        assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret_set@);
        assert(self.is_va_entry_exist(va));

        assert(page_alloc.wf());
        assert(page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages());
        assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret_set@);
        assert(page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret_set@);
        return (l1_ptr,ret_set);
}

    pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self.mapping@ =~= old(self).mapping@,
            self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.is_va_entry_exist(va),
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        let mut ret:Ghost<Set<PagePtr>> = Ghost(Set::empty());
            proof{
                pagetable_virtual_mem_lemma();  
                page_ptr_lemma();
                pagemap_permission_bits_lemma();
                // lemma_set_properties::<Set<PagePtr>>();  
            }
            let (l4i,l3i,l2i,l1i) = va2index(va);
        let (l3_ptr, l3_ret_set) = self.create_va_entry_l3(va,page_alloc,l4i,l3i,l2i,l1i);
        proof{
            ret@ = ret@ + l3_ret_set@;
        }
        let (l2_ptr, l2_ret_set) = self.create_va_entry_l2(va,page_alloc,l4i,l3i,l2i,l1i,l3_ptr);
        proof{
            ret@ = ret@ + l2_ret_set@;
        }
        let (l1_ptr, l1_ret_set) = self.create_va_entry_l1(va,page_alloc,l4i,l3i,l2i,l1i,l2_ptr);
        proof{
            ret@ = ret@ + l1_ret_set@;
        }
        return ret;
    }

    // pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
    //     requires
    //         old(self).wf(),
    //         old(page_alloc).wf(),
    //         old(page_alloc).free_pages.len() >= 4,
    //         spec_va_valid(va),
    //         old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
    //         old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
    //     ensures
    //         self.wf(),
    //         self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
    //         page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
    //         ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
    //         self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
    //         self.mapping@ =~= old(self).mapping@,
    //         self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@,
    //         self.is_va_entry_exist(va),
    //         page_alloc.wf(),
    //         page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
    //         page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
    //         page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
    //         forall|page_ptr:PagePtr| #![auto] page_alloc.available_pages@.contains(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
    // {
    //     let mut ret:Ghost<Set<PagePtr>> = Ghost(Set::empty());
    //     proof{
    //         pagetable_virtual_mem_lemma();  
    //         page_ptr_lemma();
    //         pagemap_permission_bits_lemma();
    //         // lemma_set_properties::<Set<PagePtr>>();  
    //     }
    //     let (l4i,l3i,l2i,l1i) = va2index(va);
    //     assert(l4i >= KERNEL_MEM_END_L4INDEX);
    //     assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
    //     let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
    //     let l4_tbl : &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
    //     let mut l3_option = l4_tbl.get(l4i);
    //     let mut l3_ptr = 0;
    //     if l3_option.is_none() {
    //         assert(self.is_va_entry_exist(va) == false);
    //         //alloc new page for l3 page
    //         let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
    //         assume(page_ptr != 0);
    //         assert(self.l3_tables@.dom().contains(page_ptr) == false);
    //         assert(self.cr3 != page_ptr);

    //         assert(self.l4_table@.dom().contains(self.cr3));
    //         let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
    //         assert(self.cr3 == l4_perm@.pptr);
    //         let l4_pptr = PPtr::<PageMap>::from_usize(self.cr3);

    //         assert(l4_perm@.value.get_Some_0().wf());
    //         //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

    //         l3_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});


    //         pagemap_set(&l4_pptr,Tracked(&mut l4_perm),l4i,l3_option);

    //         assert(l4_perm@.value.get_Some_0()[l4i] == l3_option);
    //         assert(l4_perm@.pptr == self.cr3);
    
    //         proof {
    //             self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
    //         }
    //         assert(self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().addr == page_ptr);
            
    //         let (l3_ptr_tmp,mut l3_perm) = page_to_pagemap((page_ptr,page_perm));
    //         proof{
    //             self.l3_tables.borrow_mut().tracked_insert(l3_ptr_tmp, l3_perm.get());
    //         }
    //         assert(self.wf_l4());

    //         assert(self.wf_l3());
            
    //         assert(self.wf_l2());

    //         assert(self.wf_l1());

    //         proof{
    //             self.wf_to_wf_mapping();
    //         }

    //         assert(self.no_self_mapping());

    //         assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j != l4i) 
    //             ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

    //         assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l4j == l4i) 
    //             ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

    //         assert(self.wf_mapping());
    //         assert(self.wf());
    //         l3_ptr = l3_ptr_tmp;
    //         proof{ret@ = ret@.insert(l3_ptr_tmp);}
    //         assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //         assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //         assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //         assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
    //     }else{
    //         l3_ptr = l3_option.unwrap().addr;
    //     }
    //     assert(self.wf());
    //     assert(self.resolve_mapping_l4(l4i) == l3_option);
    //     assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //     assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //     assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //     assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

    //     let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
    //     assert(l3_ptr == l3_perm@.pptr);
    //     let l3_tbl : &PageMap = PPtr::<PageMap>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
    //     let mut l2_option = l3_tbl.get(l3i);
    //     let mut l2_ptr:PAddr = 0;
    //     if l2_option.is_none() {
    //         assert(self.is_va_entry_exist(va) == false);
    //         //alloc new page for l2 page
    //         let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
    //         assume(page_ptr != 0);
    //         assert(self.l3_tables@.dom().contains(page_ptr) == false);

    //         assert(self.l3_tables@.dom().contains(l3_ptr));
    //         let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(l3_ptr);
    //         assert(l3_ptr == l3_perm@.pptr);
    //         let l3_pptr = PPtr::<PageMap>::from_usize(l3_ptr);

    //         assert(l3_perm@.value.get_Some_0().wf());
    //         //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

    //         l2_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});
    //         pagemap_set(&l3_pptr,Tracked(&mut l3_perm),l3i,l2_option);
    //         assert(l3_perm@.value.get_Some_0()[l3i] == l2_option);
    //         assert(l3_perm@.pptr == l3_ptr);
    
    //         proof {
    //             self.l3_tables.borrow_mut().tracked_insert(l3_ptr, l3_perm);
    //         }
    //         assert(self.l3_tables@[l3_ptr]@.value.get_Some_0()[l3i].get_Some_0().addr == page_ptr);
    //         let (l2_ptr_tmp,mut l2_perm) = page_to_pagemap((page_ptr,page_perm));
    //         proof{
    //             self.l2_tables.borrow_mut().tracked_insert(l2_ptr_tmp, l2_perm.get());
    //         }
    //         assert(self.wf_l4());
        
    //         assert(self.wf_l3());

    //         assert(self.wf_l2());

    //         assert(self.wf_l1());

    //         assert(self.no_self_mapping());

    //         assert(self.wf_mapping());
    //         assert(self.wf());

    //         l2_ptr = l2_ptr_tmp;
    //         proof{ret@ = ret@.insert(l2_ptr_tmp);}
    //         assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //         assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //         assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //         assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
    //     }else{
    //         l2_ptr = l2_option.unwrap().addr;
    //     }
    //     assert(self.wf());
    //     assert(self.resolve_mapping_l3(l4i,l3i).is_Some());
    //     assert(self.resolve_mapping_l3(l4i,l3i).get_Some_0().addr == l2_ptr);
    //     assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //     assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //     assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //     assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

    //     let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
    //     assert(l2_ptr == l2_perm@.pptr);
    //     let l2_tbl : &PageMap = PPtr::<PageMap>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
    //     let mut l1_option = l2_tbl.get(l2i);
    //     let mut l1_ptr:usize = 0;
    //     if l1_option.is_none() {
    //         assert(self.is_va_entry_exist(va) == false);
    //         //alloc new page for l2 page
    //         let (page_ptr, page_perm) = page_alloc.alloc_pagetable_mem();
    //         assume(page_ptr != 0);
    //         assert(self.l2_tables@.dom().contains(page_ptr) == false);

    //         assert(self.l2_tables@.dom().contains(l2_ptr));
    //         let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(l2_ptr);
    //         assert(l2_ptr == l2_perm@.pptr);
    //         let l2_pptr = PPtr::<PageMap>::from_usize(l2_ptr);

    //         assert(l2_perm@.value.get_Some_0().wf());
    //         //assert(l1_perm@.value.get_Some_0()[l1i as int] == 0);

    //         l1_option = Some(PageEntry{addr:page_ptr,perm:READ_WRITE_EXECUTE});
    //         pagemap_set(&l2_pptr,Tracked(&mut l2_perm),l2i,l1_option);
    //         assert(l2_perm@.value.get_Some_0()[l2i] == l1_option);
    //         assert(l2_perm@.pptr == l2_ptr);
    
    //         proof {
    //             self.l2_tables.borrow_mut().tracked_insert(l2_ptr, l2_perm);
    //         }
    //         let (l1_ptr_tmp,mut l1_perm) = page_to_pagemap((page_ptr,page_perm));
    //         proof{
    //             self.l1_tables.borrow_mut().tracked_insert(l1_ptr_tmp, l1_perm.get());
    //         }
    //         assert(self.wf_l4());
        
    //         assert(self.wf_l3());
            
    //         assert(self.wf_l2());

    //         assert(self.wf_l1());

    //         proof{
    //             self.wf_to_wf_mapping();
    //         }

    //         assert(self.no_self_mapping());

    //         assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j != l2i) 
    //             ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

    //         assert(forall|l4j: usize,l3j: usize,l2j: usize, l1j: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512 && 0<= l1j < 512 && l2j == l2i) 
    //             ==> old(self).resolve_mapping_l1(l4j,l3j,l2j,l1j) == self.resolve_mapping_l1(l4j,l3j,l2j,l1j));

    //         assert(self.wf_mapping());
    //         assert(self.wf());

    //         l1_ptr = l1_ptr_tmp;
    //         proof{ret@ = ret@.insert(l1_ptr_tmp);}
    //         assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //         assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //         assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //         assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));
    //     }else{
    //         l1_ptr = l1_option.unwrap().addr;
    //     }
    //     assert(self.wf());
    //     assert(self.resolve_mapping_l2(l4i,l3i,l2i).is_Some());
    //     assert(self.resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr == l1_ptr);
    //     assert(self.resolve_mapping_l2(l4i,l3i,l2i) =~= l1_option);
    //     assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //     assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //     assert(ret@.subset_of(old(page_alloc).get_free_pages_as_set()));
    //     assert(self.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()));

    //     assert(self.mapping@ =~= old(self).mapping@);
    //     assert(self.get_pagetable_page_closure() =~= old(self).get_pagetable_page_closure() + ret@);
    //     assert(self.is_va_entry_exist(va));

    //     assert(page_alloc.wf());
    //     assert(page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages());
    //     assert(page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@);
    //     assert(page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@);
    //     return ret;
    // }

/*
    // pub fn unmap_page_no_lookup(&mut self,page_alloc :&mut PageAllocator, l4i:usize, l3i:usize, l2i:usize, l1i:usize,  l3_ptr:usize, l2_ptr:usize, l1_ptr:usize)
    //     requires
    //         old(self).wf(),
    //         KERNEL_MEM_END_L4INDEX <= l4i < 512,
    //         0 <= l3i < 512,
    //         0 <= l2i < 512,
    //         0 <= l1i < 512,
    //         old(self).l4_entry_exists(l4i),
    //         old(self).l3_entry_exists(l4i,l3i),
    //         old(self).l2_entry_exists(l4i,l3i,l2i),
    //         old(self).resolve_mapping_l4(l4i) == l3_ptr,
    //         old(self).resolve_mapping_l3(l4i,l3i) == l2_ptr,
    //         old(self).resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr,
    //         old(self).resolve_mapping_l2(l4i,l3i,l2i) != 0,
    //     ensures
    //         self.wf(),
    //         self.l4_entry_exists(l4i),
    //         self.l3_entry_exists(l4i,l3i),
    //         self.l2_entry_exists(l4i,l3i,l2i),
    //         self.resolve_mapping_l4(l4i) == l3_ptr,
    //         self.resolve_mapping_l3(l4i,l3i) == l2_ptr,
    //         self.resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr,
    //         self.resolve_mapping_l2(l4i,l3i,l2i) != 0,
    //         forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
    //             self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))],
    //         self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))] == 0,
    //         forall|j:usize| 0<=j<512 && j != l1i ==> 
    //             self.l1_tables@[l1_ptr]@.value.get_Some_0()[j as int] == old(self).l1_tables@[l1_ptr]@.value.get_Some_0()[j as int],
    //         self.l1_tables@[l1_ptr]@.value.get_Some_0()[l1i as int] == 0,

    // {
    //     proof{
    //         pagetable_virtual_mem_lemma();
    //     }
    //     assert(self.l1_tables@.dom().contains(l1_ptr));
    //     let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
    //     assert(l1_ptr == l1_perm@.pptr);
    //     let l1_pptr = PPtr::<PageMap>::from_usize(l1_ptr);

    //     assert(l1_perm@.value.get_Some_0().table.wf());
    //     assert(l1_perm@.pptr == l1_ptr);
    //     pagemap_set(&l1_pptr,Tracked(&mut l1_perm),l1i,0);
    //     proof {self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),0);}

    //     proof {self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);}

    //     assert(self.wf_l4());

    //     assert(self.wf_l3());
        
    //     assert(self.wf_l2());

    //     assert(self.wf_l1());

    //     proof{
    //         self.wf_to_wf_mapping();
    //     }

    //     assert(self.no_self_mapping());

    //     assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == 0);

    //     assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
    //         self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

    //     assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
    //         self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
    //     );

    //     assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) == l1_ptr && _l1i != l1i==> (
    //         self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
    //     );

    //     assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
    //         self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
    //     );

    //     assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
    //         self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
    //     );

    //     assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] KERNEL_MEM_END_L4INDEX<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && _l1i != l1i ==> (
    //         self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
    //     );

    //     assert(self.wf_mapping());

    //     assert(self.wf());
    // }
    */

    pub fn init_to_wf(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, kernel_pml4_entry: Option<PageEntry>)
        requires
            old(self).wf_mapping(),
            old(self).get_pagetable_page_closure() =~= Set::empty(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> old(self).get_pagetable_mapping()[va].is_None(),
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.get_pagetable_mapping()[va].is_None(),
            self.get_pagetable_page_closure() =~= Set::empty().insert(page_ptr),

    {
        proof{
            pagetable_virtual_mem_lemma();
        }
        assert(self.l4_table@.dom() =~= Set::empty());
        assert(self.l3_tables@.dom() =~= Set::empty());
        assert(self.l2_tables@.dom() =~= Set::empty());
        assert(self.l1_tables@.dom() =~= Set::empty());
        self.cr3 = page_ptr;
        let (l4_ptr,mut l4_perm) = page_to_pagemap((page_ptr,page_perm));
        assume(kernel_pml4_entry.is_None());
        
        proof{
            self.l4_table.borrow_mut().tracked_insert(l4_ptr, l4_perm.get());
        }

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(l4_ptr);

        pagemap_set(&PPtr::<PageMap>::from_usize(l4_ptr),Tracked(&mut l4_perm),0,kernel_pml4_entry);

        proof{self.l4_table.borrow_mut().tracked_insert(l4_ptr, l4_perm);}

        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2());
        assert(self.wf_l1());
        assert(self.no_self_mapping());
        assert(self.wf_mapping());
        assert(self.l4_kernel_entries_reserved());

        assert(self.wf());

    }

}

}