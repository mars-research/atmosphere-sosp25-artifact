use super::*;

// use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::ptr::*;

use crate::mars_staticlinkedlist::*;

use crate::setters::*;
use crate::define::*;
// use vstd::set_lib::lemma_set_properties;
// use vstd::seq_lib::lemma_seq_properties;


verus! {

pub struct Process{
    // pub owned_threads: LinkedList<ThreadPtr>,
    // pub pl_rf: NodeRef<ProcPtr>,
    pub pl_rf: Index,
    pub pcid: Pcid,
    pub owned_threads: MarsStaticLinkedList<MAX_NUM_THREADS_PER_PROC>,
}

impl Process {
    pub open spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub open spec fn get_pcid(&self) -> Pcid {
        self.pcid
    }
}

impl ProcessManager {
    pub fn new_proc(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, new_pcid: Pcid) -> (ret: ProcPtr)
        requires
            old(self).wf(),
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
            old(self).get_proc_ptrs().len() < MAX_NUM_PROCS,
            old(self).page_closure().contains(page_ptr) == false,
            old(self).pcid_closure().contains(new_pcid) == false,
        ensures
            self.wf(),
            self.scheduler =~= old(self).scheduler,
            self.pcid_closure() =~= old(self).pcid_closure().insert(new_pcid),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs().push(ret),
            self.get_proc_ptrs().contains(ret),
            self.page_closure() =~= old(self).page_closure().insert(ret),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.proc_perms@[ret]@.value.get_Some_0().owned_threads.len() == 0,
    {
        assert(forall|_endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(_endpoint_ptr) 
    ==>  (forall|_thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[_endpoint_ptr]@.value.get_Some_0().queue@.contains(_thread_ptr)
        ==> (
            (self.thread_perms@.dom().contains(_thread_ptr))
            &&
            (self.thread_perms@[_thread_ptr]@.value.get_Some_0().state == BLOCKED)
            &&
            (self.thread_perms@[_thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() == _endpoint_ptr)
        )
));
        assert(self.proc_ptrs@.contains(page_ptr) == false);
        let ret = page_ptr;
        let (proc_pptr,mut proc_perm) = page_to_proc((PPtr::<[u8; PAGE_SIZE]>::from_usize(page_ptr),page_perm));

        let proc_ptr = proc_pptr.to_usize();

        proc_perm_init(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm);
        assert(proc_perm@@.value.get_Some_0().owned_threads.wf());

        assert(self.proc_ptrs.wf());
        assert(self.proc_ptrs.size == MAX_NUM_PROCS);

        let pl_rf = self.proc_ptrs.push(ret);
        
        proc_set_pl_rf(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, pl_rf);
        proc_set_pcid(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, new_pcid);


        assert(self.proc_perms@.dom().contains(ret) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(ret, proc_perm.get());
        }

        proof{
            self.pcid_closure@ = self.pcid_closure@.insert(new_pcid);}

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.endpoint_ptrs@ =~= self.endpoint_perms@.dom());
        assert(self.endpoint_perms@.dom().contains(0) == false);
        assert(self.wf_endpoints());
        assert(self.wf());

        return ret;
    }

    pub fn free_proc(&mut self, proc_ptr: ProcPtr) -> (ret: (PagePPtr,Tracked<PagePerm>))
        requires
            old(self).wf(),
            old(self).get_proc_ptrs().contains(proc_ptr),    
            old(self).get_proc(proc_ptr).owned_threads.len() == 0,
    {
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked mut proc_perm =
            (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr);
        let pl_rf = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(&proc_perm)).pl_rf;
        let pcid = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(&proc_perm)).pcid;
        let removed_proc_ptr = self.proc_ptrs.remove(pl_rf);
        assert(removed_proc_ptr == proc_ptr);
        proof{
            self.pcid_closure@ = self.pcid_closure@.remove(pcid);
        }
        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf());

        return proc_to_page((PPtr::<Process>::from_usize(proc_ptr), Tracked(proc_perm)));
    }
}
}