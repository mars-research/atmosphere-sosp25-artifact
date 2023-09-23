use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::ptr::PointsTo;
use vstd::ptr::PPtr;

use crate::linked_list::*;
use crate::page::{PagePPtr,Pcid};
use crate::pcid_alloc::PCID_MAX;
use crate::sched::{Scheduler, Endpoint};
use crate::mars_array::MarsArray;
use crate::mars_staticlinkedlist::*;

pub type ThreadState = usize;
pub const SCHEDULED:usize = 1;
pub const BLOCKED:usize = 2;
pub const RUNNING:usize = 3;

pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointPtr = usize;

pub const MAX_NUM_ENDPOINT_DESCRIPTORS:usize = 32;
pub const MAX_NUM_THREADS_PER_PROC:usize = 500;
pub const MAX_NUM_PROCS:usize = PCID_MAX;
pub const MAX_NUM_THREADS:usize = 500 * 4096;

pub struct Process{
    // pub owned_threads: LinkedList<ThreadPtr>,
    // pub pl_rf: NodeRef<ProcPtr>,

    pub owned_threads: MarsStaticLinkedList<MAX_NUM_THREADS_PER_PROC>,
    pub pl_rf: Index,
    pub pcid: Pcid,
}

pub struct Thread{
    pub parent: ProcPtr,
    pub state: ThreadState,

    // pub parent_rf: NodeRef<ThreadPtr>,
    // pub scheduler_rf: Option<NodeRef<ThreadPtr>>,
    // pub endpoint_ptr: Option<NodeRef<ThreadPtr>>,

    pub parent_rf: Index,
    pub scheduler_rf: Option<Index>,
    pub endpoint_ptr: Option<Index>,

    pub endpoint_descriptors: MarsArray<EndpointPtr,MAX_NUM_ENDPOINT_DESCRIPTORS>,
}

pub struct ProcessManager{
    // pub proc_ptrs: LinkedList<ProcPtr>,
    pub proc_ptrs: MarsStaticLinkedList<MAX_NUM_PROCS>,
    pub proc_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,

    pub thread_ptrs: Ghost<Set<ThreadPtr>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    
    //pub scheduler: Scheduler,
    pub scheduler: MarsStaticLinkedList<MAX_NUM_THREADS>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,

}

verus! {

#[verifier(external_body)]
pub fn thread_set_scheduler_rf(pptr: &PPtr::<Thread>,Tracked(perm): Tracked<&mut PointsTo<Thread>>, scheduler_rf: Option<Index>)
    requires pptr.id() == old(perm)@.pptr,
                old(perm)@.value.is_Some(),
    ensures pptr.id() == perm@.pptr,
            perm@.value.is_Some(),
            perm@.value.get_Some_0().parent == old(perm)@.value.get_Some_0().parent,
            perm@.value.get_Some_0().state == old(perm)@.value.get_Some_0().state,
            perm@.value.get_Some_0().parent_rf == old(perm)@.value.get_Some_0().parent_rf,
            //perm@.value.get_Some_0().scheduler_rf == old(perm)@.value.get_Some_0().scheduler_rf,
            perm@.value.get_Some_0().endpoint_ptr == old(perm)@.value.get_Some_0().endpoint_ptr,
            perm@.value.get_Some_0().endpoint_descriptors == old(perm)@.value.get_Some_0().endpoint_descriptors,
            perm@.value.get_Some_0().scheduler_rf == scheduler_rf,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().scheduler_rf = scheduler_rf;
    }
}

#[verifier(external_body)]
pub fn thread_set_state(pptr: &PPtr::<Thread>,Tracked(perm): Tracked<&mut PointsTo<Thread>>, state: ThreadState)
    requires pptr.id() == old(perm)@.pptr,
                old(perm)@.value.is_Some(),
    ensures pptr.id() == perm@.pptr,
            perm@.value.is_Some(),
            perm@.value.get_Some_0().parent == old(perm)@.value.get_Some_0().parent,
            //perm@.value.get_Some_0().state == old(perm)@.value.get_Some_0().state,
            perm@.value.get_Some_0().parent_rf == old(perm)@.value.get_Some_0().parent_rf,
            perm@.value.get_Some_0().scheduler_rf == old(perm)@.value.get_Some_0().scheduler_rf,
            perm@.value.get_Some_0().endpoint_ptr == old(perm)@.value.get_Some_0().endpoint_ptr,
            perm@.value.get_Some_0().endpoint_descriptors == old(perm)@.value.get_Some_0().endpoint_descriptors,
            perm@.value.get_Some_0().state == state,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().state = state;
    }
}

impl Process {
    pub closed spec fn page_closure(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

    pub closed spec fn get_pcid(&self) -> Pcid {
        self.pcid
    }
}

impl Thread {
    pub closed spec fn page_closure(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

}

impl ProcessManager {

    // pub closed spec fn get_procs(&self) -> Seq<Process>
    // {
    //     Seq::new(self.proc_ptrs@.len(), |i: int| self.proc_perms@[self.proc_ptrs@[i]]@.value.get_Some_0())
    // }

    pub closed spec fn get_proc_ptrs(&self) -> Seq<ProcPtr>
    {
        Seq::new(self.proc_ptrs@.len(), |i: int| self.proc_ptrs@[i])
    }

    pub closed spec fn get_proc(&self, proc_ptr: ProcPtr) -> Process
        recommends
            self.get_proc_ptrs().contains(proc_ptr),
    {
        self.proc_perms@[proc_ptr]@.value.get_Some_0()
    }

    pub closed spec fn get_thread_ptrs(&self) -> Set<ThreadPtr>
    {
        self.thread_ptrs@
    }

    pub closed spec fn get_thread(&self, thread_ptr:ThreadPtr) -> Thread
        recommends
            self.get_thread_ptrs().contains(thread_ptr)
    {
        self.thread_perms@[thread_ptr].view().value.get_Some_0()
    }
    ///spec helper for processes
    ///specs: 
    ///Process list (PL) contains no duplicate process pointers
    ///PM contains and only contains process perms of its process pointers
    ///Each process contains no duplicate thread pointers
    ///Each process's threads are disjoint
    ///Each process owns a valid reverse pointer to free it from PL
    pub closed spec fn wf_procs(&self) -> bool{
        (self.proc_ptrs.wf())
        &&            
        (self.proc_ptrs.unique())
        &&
        (self.proc_ptrs@.to_set() =~= self.proc_perms@.dom())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.is_Some())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().pptr == proc_ptr)
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.wf())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.unique())
        &&
        (forall|proc_ptr_i: ProcPtr, proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j) ==>
            self.proc_perms@[proc_ptr_i].view().value.get_Some_0().owned_threads@.to_set().disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().owned_threads@.to_set()))
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_ptrs.node_ref_valid(self.proc_perms@[proc_ptr].view().value.get_Some_0().pl_rf))
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_ptrs.node_ref_resolve(self.proc_perms@[proc_ptr].view().value.get_Some_0().pl_rf) == proc_ptr)
    }

    ///spec helper for threads
    ///specs: 
    ///PM contains and only contains thread perms of threads owned by some processes
    ///Each thread has a parent which owns this thread in its owned_threads list
    ///Each process owns a valid reverse pointer to free it from its parent process's owned_threads list
    ///Each process owns a valid reverse pointer to free it from the scheduler
    ///Each process owns a valid reverse pointer to free it from the endpoints
    pub closed spec fn wf_threads(&self) -> bool{
        (self.get_thread_ptrs() =~= self.thread_perms@.dom())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().pptr == thread_ptr)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  0 <= self.thread_perms@[thread_ptr].view().value.get_Some_0().state <= 3)
        && 
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_ptrs@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent))
        && 
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads@.contains(thread_ptr))
        && 
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  
            self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf))
        && 
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  
            self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf) == thread_ptr)
        && 
        (forall|proc_ptr: usize, thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
            ==>  self.thread_perms@.dom().contains(thread_ptr))
        && 
        (forall|proc_ptr: usize, thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
            ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().parent == proc_ptr)
        
    }

    pub closed spec fn wf_scheduler(&self) -> bool{
        (self.scheduler.wf())
        &&
        (self.scheduler.unique())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@.dom().contains(thread_ptr))
        // &&
        // (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.get_thread_ptrs().contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.get_Some_0().state == SCHEDULED)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()) == thread_ptr )
    }

    closed spec fn local_page_closure(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

    pub closed spec fn page_closure(&self) -> Set<PagePPtr>
    {
        self.local_page_closure()
        +
        self.proc_ptrs@.fold_left(Set::<PagePPtr>::empty(), |acc: Set::<PagePPtr>, e: ProcPtr| -> Set::<PagePPtr> {
                acc + self.proc_perms@[e]@.value.get_Some_0().page_closure()
        })
        +
        self.get_thread_ptrs().fold(Set::<PagePPtr>::empty(), |acc: Set::<PagePPtr>, e: ThreadPtr| -> Set::<PagePPtr> {
                acc + self.thread_perms@[e]@.value.get_Some_0().page_closure()
        })
        // + ... fold page closures of other PM components
    }

    pub closed spec fn pcid_closure(&self) -> Set<Pcid>
    {
        Seq::new(self.proc_ptrs@.len(), |i: int| self.proc_perms@[self.proc_ptrs@[i]]@.value.get_Some_0().get_pcid()).to_set()
    }

    ///Memory spec helper
    ///specs:
    ///For two different Processes, their page closures are disjoint.
    ///For any process, its data closure is disjoint with any page closure of the system.
    pub closed spec fn wf_mem_closure(&self) -> bool{
        true

        // (
        //     forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
        //         ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().page_closure@.disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().page_closure@)
        // )
        // &&
        // (
        //     forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
        //         ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().data_page_closure@.disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().page_closure@)
        // )

    }

    pub closed spec fn wf_pcid_closure(&self) -> bool{
        (
            forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
                ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_pcid() != self.proc_perms@[proc_ptr_j].view().value.get_Some_0().get_pcid()
        )
    }

    pub closed spec fn wf(&self) -> bool{
        self.wf_threads()
        &&
        self.wf_procs()
        &&
        self.wf_scheduler()
        &&
        self.wf_mem_closure()
        &&
        self.wf_pcid_closure()
    }

    pub fn push_scheduler(&mut self, thread_ptr: ThreadPtr)
        requires 
            old(self).wf(),
            old(self).scheduler.len() < MAX_NUM_THREADS,
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state != 1,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.get_thread(thread_ptr).state == 1,
            self.scheduler.len() == old(self).scheduler.len() + 1,
            // self.proc_ptrs =~= old(self).proc_ptrs,
            // self.proc_perms =~= old(self).proc_perms,
            // self.thread_ptrs =~= old(self).thread_ptrs,
            // forall|_thread_ptr:ThreadPtr| #![auto] _thread_ptr != thread_ptr && self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr] =~= old(self).thread_perms@[_thread_ptr],
    {
        
        let ret = self.scheduler.push(thread_ptr);
        let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
        let tracked mut thread_perm: PointsTo<Thread> =
            (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr);
        thread_set_scheduler_rf(&thread_pptr, Tracked(&mut thread_perm), Some(ret));
        thread_set_state(&thread_pptr, Tracked(&mut thread_perm), SCHEDULED);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm);
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
    }

    pub fn pop_scheduler(&mut self) -> (ret: ThreadPtr)
        requires 
            old(self).wf(),
            old(self).scheduler.len() > 0,
        ensures
            self.wf(),
            self.get_thread_ptrs().contains(ret),
            self.scheduler@.contains(ret) == false,
            old(self).get_thread(ret).state == 1,
            // self.proc_ptrs =~= old(self).proc_ptrs,
            // self.proc_perms =~= old(self).proc_perms,
            // self.thread_ptrs =~= old(self).thread_ptrs,
            // self.thread_perms =~= old(self).thread_perms,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
    {
        let ret = self.scheduler.pop();

        assert(old(self).scheduler@[0] == ret);
        assert(old(self).scheduler@.contains(ret));
        assert(self.thread_perms@.dom().contains(ret));

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        return ret;
    }

    pub fn set_thread_state(&mut self, thread_ptr:ThreadPtr, state:ThreadState)
        requires 
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).scheduler@.contains(thread_ptr) == false,
            0<=state<=3,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.get_thread(thread_ptr).state == state,
    {
        let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
        let tracked mut thread_perm: PointsTo<Thread> =
            (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr);
        thread_set_state(&thread_pptr, Tracked(&mut thread_perm), state);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm);
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
    }

}
}