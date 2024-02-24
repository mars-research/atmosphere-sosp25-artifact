use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;

use crate::pagetable::*;



// TODO: @Xiangdong create real IOMMUTable impl. But it is OK to re-use our pagetable for now.
pub struct IOMMUTable{
    pub dummy: PageTable,
}

impl IOMMUTable{
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool{
        self.dummy.wf()
    }
    #[verifier(inline)]
    pub open spec fn wf_mapping(&self) -> bool{
        self.dummy.wf_mapping()
    }

    #[verifier(inline)]
    pub open spec fn get_iommutable_page_closure(&self) -> Set<PagePtr> {
        self.dummy.get_pagetable_page_closure()
    }

    #[verifier(inline)]
    pub open spec fn get_iommutable_mapping(&self) -> Map<usize,Option<PageEntry>> {
        self.dummy.get_pagetable_mapping()
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_mapped_pages(&self) -> Set<PagePtr>{
        self.dummy.get_pagetable_mapped_pages()
    }
    #[verifier(inline)]
    pub open spec fn is_va_entry_exist(&self, va: VAddr) -> bool
        recommends
            spec_va_valid(va),    
    {
        self.dummy.is_va_entry_exist(va)
    }

    pub fn init(&mut self)
    requires
        old(self).dummy.l4_table@ =~= Map::empty(),
        old(self).dummy.l3_tables@ =~= Map::empty(),
        old(self).dummy.l2_tables@ =~= Map::empty(),
        old(self).dummy.l1_tables@ =~= Map::empty(),
    ensures
        self.dummy.wf_mapping(),
        self.dummy.get_pagetable_page_closure() =~= Set::empty(),
        self.dummy.l4_table@ =~= Map::empty(),
        self.dummy.l3_tables@ =~= Map::empty(),
        self.dummy.l2_tables@ =~= Map::empty(),
        self.dummy.l1_tables@ =~= Map::empty(),
        forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.dummy.mapping@.dom().contains(va),
        forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.dummy.mapping@[va].is_None(),
    {
        self.dummy.init();
    }
}

}