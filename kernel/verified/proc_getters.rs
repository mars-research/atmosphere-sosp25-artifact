use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SZ,
};

//use crate::linked_list::*;

use crate::pcid_alloc::PCID_MAX;
// use crate::sched::{Scheduler};
use crate::mars_array::MarsArray;
use crate::mars_staticlinkedlist::*;

use crate::setters::*;
use crate::define::*;
// use vstd::set_lib::lemma_set_properties;
// use vstd::seq_lib::lemma_seq_properties;

use crate::proc::*;

verus!{

impl ProcessManager{

    pub fn check_endpoint_rf_counter(&self, endpoint_ptr: EndpointPtr) -> (ret: usize)
    requires
        self.wf(),
        self.get_endpoint_ptrs().contains(endpoint_ptr),
    ensures
        ret == self.get_endpoint(endpoint_ptr).rf_counter,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        return endpoint.rf_counter;
    }
}

}