use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;
    use crate::process_manager::container::Container;
    use vstd::simple_pptr::*;
    use crate::lemma::lemma_u::*;
    use crate::lemma::lemma_t::*;
    use crate::process_manager::container_util_t::*;
    use crate::process_manager::spec_impl::ProcessManager;
    use crate::process_manager::process::Process;

    //specs
    impl ProcessManager{
        pub open spec fn proc_dom(&self) -> Set<ProcPtr>
        {
            self.process_perms@.dom()
        }

        pub open spec fn spec_get_proc(&self, p_ptr:ProcPtr) -> &Process
        {
            &self.process_perms@[p_ptr].value()
        }

        #[verifier(when_used_as_spec(spec_get_proc))]
        pub fn get_proc(&self, proc_ptr:ProcPtr) -> (ret:&Process)
            requires
                self.processes_perms_wf(),
                self.proc_dom().contains(proc_ptr),
            ensures
                self.get_proc(proc_ptr) == ret,
        {
            let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
            let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
            proc
        }

        pub closed spec fn processes_perms_wf(&self) -> bool{
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].is_init()]
                #![trigger self.process_perms@[p_ptr].addr()]
                self.process_perms@.dom().contains(p_ptr)
                ==>
                self.process_perms@[p_ptr].is_init()
                &&            
                self.process_perms@[p_ptr].addr() == p_ptr
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].value().children.wf()]
                self.process_perms@.dom().contains(p_ptr)
                ==> 
                self.process_perms@[p_ptr].value().children.wf()
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].value().children.unique()]
                self.process_perms@.dom().contains(p_ptr)
                ==> 
                self.process_perms@[p_ptr].value().children.unique()
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].value().uppertree_seq@.no_duplicates()]
                self.process_perms@.dom().contains(p_ptr)
                ==> 
                self.process_perms@[p_ptr].value().uppertree_seq@.no_duplicates()
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@.dom().contains(p_ptr), self.process_perms@[p_ptr].value().children@.contains(p_ptr)]
                self.process_perms@.dom().contains(p_ptr)
                ==>
                self.process_perms@[p_ptr].value().children@.contains(p_ptr) == false
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].value().subtree_set@.finite()]
                self.process_perms@.dom().contains(p_ptr)
                ==>
                self.process_perms@[p_ptr].value().subtree_set@.finite()
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@[p_ptr].value().uppertree_seq@.len(), self.process_perms@[p_ptr].value().depth]
                self.process_perms@.dom().contains(p_ptr)
                ==>
                self.process_perms@[p_ptr].value().uppertree_seq@.len() == self.process_perms@[p_ptr].value().depth    
        }

        pub closed spec fn processes_container_wf(&self) -> bool{
        // &&&
        // forall|c_ptr:ContainerPtr| 
        //     #![trigger self.container_tree.get_container(c_ptr).owned_procs]
        //     self.container_tree.container_dom().contains(c_ptr)
        //     ==>
        //     self.container_tree.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
            #![trigger self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)
            ==> self.process_perms@.dom().contains(child_p_ptr)
                &&
                self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@[p_ptr].value().owning_container]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.container_dom().contains(self.process_perms@[p_ptr].value().owning_container)
            &&
            self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs@.to_set().contains(p_ptr)
            &&
            self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            &&
            self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
        }

        pub closed spec fn processes_root_wf(&self, container_ptr: ContainerPtr) -> bool
            recommends
                self.container_perms@.dom().contains(container_ptr),
        {
            &&&
            self.container_perms@[container_ptr].value().owned_procs@.len() != 0
            &&&
            self.container_perms@[container_ptr].value().owned_procs@.contains(self.container_perms@[container_ptr].value().root_process)
            &&&
            self.get_proc(self.get_container(container_ptr).root_process).depth == 0
            &&&
            self.get_proc(self.get_container(container_ptr).root_process).parent.is_None()
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.get_container(container_ptr).owned_procs@.contains(p_ptr), self.get_proc(p_ptr).depth]
                #![trigger self.get_proc(p_ptr).parent.is_Some()]
                self.get_container(container_ptr).owned_procs@.contains(p_ptr)
                &&
                p_ptr != self.get_container(container_ptr).root_process
                ==>
                self.get_proc(p_ptr).depth != 0
                &&
                self.get_proc(p_ptr).parent.is_Some()
        }

        pub closed spec fn process_childern_list_wf(&self, container_ptr: ContainerPtr) -> bool
            recommends
                self.container_perms@.dom().contains(container_ptr),
        {
            &&&
            forall|p_ptr:ProcPtr, child_p_ptr:ProcPtr| 
                #![trigger self.get_proc(p_ptr).children@.contains(child_p_ptr), self.get_proc(p_ptr).depth, self.get_proc(child_p_ptr).depth]
                #![trigger self.container_perms@.dom().contains(p_ptr), self.get_proc(p_ptr).children@.contains(child_p_ptr), self.proc_dom().contains(child_p_ptr)]
                #![trigger self.get_proc(p_ptr).children@.contains(child_p_ptr), self.get_proc(child_p_ptr).parent.unwrap()]
                self.get_container(container_ptr).owned_procs@.contains(p_ptr) 
                && 
                self.get_proc(p_ptr).children@.contains(child_p_ptr)
                ==> self.proc_dom().contains(child_p_ptr)
                    &&
                    self.get_proc(child_p_ptr).parent.unwrap() == p_ptr
                    &&
                    self.get_proc(p_ptr).depth == self.get_proc(child_p_ptr).depth + 1
        }

        pub closed spec fn processes_linkedlist_wf(&self, container_ptr: ContainerPtr) -> bool
            recommends
                self.container_perms@.dom().contains(container_ptr),
        {
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.proc_dom().contains(self.get_proc(p_ptr).parent.unwrap())]
                self.get_container(container_ptr).owned_procs@.contains(p_ptr) && p_ptr != self.get_container(container_ptr).root_process
                ==> 
                self.proc_dom().contains(self.get_proc(p_ptr).parent.unwrap())
            &&&
            forall|p_ptr:ProcPtr| 
                #![trigger self.get_proc(p_ptr).parent_rev_ptr.is_Some()]
                #![trigger self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children@.contains(p_ptr)]
                #![trigger self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children.node_ref_valid(self.get_proc(p_ptr).parent_rev_ptr.unwrap())]
                #![trigger self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children.node_ref_resolve(self.get_proc(p_ptr).parent_rev_ptr.unwrap())]
                self.get_container(container_ptr).owned_procs@.contains(p_ptr) && p_ptr != self.get_container(container_ptr).root_process
                ==> 
                self.get_proc(p_ptr).parent_rev_ptr.is_Some()
                &&
                self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children@.contains(p_ptr)
                && 
                self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children.node_ref_valid(self.get_proc(p_ptr).parent_rev_ptr.unwrap())
                && 
                self.get_proc(self.get_proc(p_ptr).parent.unwrap()).children.node_ref_resolve(self.get_proc(p_ptr).parent_rev_ptr.unwrap()) == p_ptr
        }

    }
}