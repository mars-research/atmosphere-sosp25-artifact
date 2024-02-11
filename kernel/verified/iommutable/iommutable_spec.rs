use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;

use crate::pagetable::*;

verus!{

// TODO: @Xiangdong create real IOMMUTable impl. But it is OK to re-use our pagetable for now.
pub struct IOMMUTable{
    pub dummy: PageTable,
}

impl IOMMUTable{
    pub open spec fn wf(&self) -> bool{
        self.dummy.wf()
    }

    pub open spec fn wf_mapping(&self) -> bool{
        self.dummy.wf_mapping()
    }


    pub open spec fn get_iommutable_page_closure(&self) -> Set<PagePtr> {
        self.dummy.get_pagetable_page_closure()
    }

    
    pub open spec fn get_iommutable_mapping(&self) -> Map<usize,Option<PageEntry>> {
        self.dummy.get_pagetable_mapping()
    }

    pub open spec fn get_iommutable_mapped_pages(&self) -> Set<PagePtr>{
        self.dummy.get_pagetable_mapped_pages()
    }

}

}