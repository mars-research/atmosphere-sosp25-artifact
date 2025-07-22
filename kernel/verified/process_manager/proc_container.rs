use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::array_set::*;
use crate::process_manager::process::Process;
use crate::process_manager::process::Container;
use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::process_manager::proc_util_t::*;
use crate::process_manager::spec_proof::ProcessManager;

pub closed spec fn processes_container_wf(&self) -> bool {
    // &&&
    // forall|c_ptr:ContainerPtr|
    //     #![trigger self.get_container(c_ptr).owned_procs]
    //     self.container_dom().contains(c_ptr)
    //     ==>
    //     self.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
    &&& forall|c_ptr: ContainerPtr, child_p_ptr: ProcPtr|
        #![trigger self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
        self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_procs@.contains(
            child_p_ptr,
        ) ==> self.process_perms@.dom().contains(child_p_ptr)
            && self.process_perms@[child_p_ptr].value().owning_container == c_ptr
    &&& forall|p_ptr: ProcPtr|
        #![trigger self.process_perms@[p_ptr].value().rev_ptr]
        #![trigger self.container_dom().contains(self.process_perms@[p_ptr].value().owning_container)]
    // #![trigger self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs]

        self.process_perms@.dom().contains(p_ptr) ==> self.container_dom().contains(
            self.process_perms@[p_ptr].value().owning_container,
        ) && self.get_container(
            self.process_perms@[p_ptr].value().owning_container,
        ).owned_procs@.to_set().contains(p_ptr) && self.get_container(
            self.process_perms@[p_ptr].value().owning_container,
        ).owned_procs.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            && self.get_container(
            self.process_perms@[p_ptr].value().owning_container,
        ).owned_procs.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
}

} // verus!
