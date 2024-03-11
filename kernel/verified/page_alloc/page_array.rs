use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::page_alloc::*;

use crate::mars_array::*;

impl<const N: usize> MarsArray<Page, N> {

    #[verifier(external_body)]
    pub fn set_page_start(&mut self, index: usize, start: PagePtr)
        requires
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            //self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].start =~= start,
            self.wf(),
    {
        self.ar[index].start = start;
    }

    #[verifier(external_body)]
    pub fn set_page_state(&mut self, index: usize, state: PageState)
        requires
            0 <= index < N,
            state <= MAPPED,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            //self@[index].state =~= old(self)@[index].state,
            self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].state =~= state,
            self.wf(),
    {
        self.ar[index].state = state;
    }

    #[verifier(external_body)]
    pub fn set_get_page_is_io_page(&mut self, index: usize, is_io_page: bool)
        requires
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            // self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].is_io_page =~= is_io_page,
            self.wf(),
    {
        self.ar[index].is_io_page = is_io_page;
    }

    #[verifier(external_body)]
    pub fn set_page_rf_count(&mut self, index: usize, rf_count: usize)
        requires
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            //self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].rf_count =~= rf_count,
            self.wf(),
    {
        self.ar[index].rf_count = rf_count;
    }

    #[verifier(external_body)]
    pub fn set_page_mappings(&mut self, index: usize, mappings: Ghost<Map<(Pcid,VAddr),PageType>>)
        requires
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            //self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].mappings =~= mappings,
            self.wf(),
    {
        self.ar[index].mappings = mappings;
    }

    #[verifier(external_body)]
    pub fn set_page_io_mappings(&mut self, index: usize, io_mappings: Ghost<Map<(IOid,VAddr),PageType>>)
        requires
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].is_io_page =~= old(self)@[index as int].is_io_page,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            // self@[index as int].io_mappings =~= old(self)@[index as int].io_mappings,
            self@[index as int].io_mappings =~= io_mappings,
            self.wf(),
    {
        self.ar[index].io_mappings = io_mappings;
    }
}
}
