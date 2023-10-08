use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SIZE,
};

use crate::linked_list::*;
use crate::page::{PagePtr,Pcid,PagePPtr,PagePerm};
use crate::pcid_alloc::PCID_MAX;
use crate::sched::{Scheduler};
use crate::mars_array::MarsArray;
use crate::mars_staticlinkedlist::*;

use crate::seters::*;

verus! {
pub type ThreadState = usize;
pub const SCHEDULED:usize = 1;
pub const BLOCKED:usize = 2;
pub const RUNNING:usize = 3;
pub const TRANSIT:usize = 4;

pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointPtr = usize;

pub const MAX_NUM_ENDPOINT_DESCRIPTORS:usize = 32;
pub const MAX_NUM_THREADS_PER_PROC:usize = 500;
pub const MAX_NUM_THREADS_PER_ENDPOINT:usize = 500;
pub const MAX_NUM_PROCS:usize = PCID_MAX;
pub const MAX_NUM_THREADS:usize = 500 * 4096;

pub struct Process{
    // pub owned_threads: LinkedList<ThreadPtr>,
    // pub pl_rf: NodeRef<ProcPtr>,
    pub pl_rf: Index,
    pub pcid: Pcid,
    pub owned_threads: MarsStaticLinkedList<MAX_NUM_THREADS_PER_PROC>,
}

pub struct Thread{
    pub parent: ProcPtr,
    pub state: ThreadState,

    // pub parent_rf: NodeRef<ThreadPtr>,
    // pub scheduler_rf: Option<NodeRef<ThreadPtr>>,
    // pub endpoint_rf: Option<NodeRef<ThreadPtr>>,

    pub parent_rf: Index,
    pub scheduler_rf: Option<Index>,
    
    pub endpoint_ptr: Option<EndpointPtr>,
    pub endpoint_rf: Option<Index>,

    pub endpoint_descriptors: MarsArray<EndpointPtr,MAX_NUM_ENDPOINT_DESCRIPTORS>,
}

pub struct Endpoint{
    pub queue: MarsStaticLinkedList<MAX_NUM_THREADS_PER_ENDPOINT>,
    pub rf_counter: usize,

    pub owning_threads: Ghost<Set<ThreadPtr>>,
}

pub struct ProcessManager{
    // pub proc_ptrs: LinkedList<ProcPtr>,
    pub proc_ptrs: MarsStaticLinkedList<MAX_NUM_PROCS>,
    pub proc_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,

    pub thread_ptrs: Ghost<Set<ThreadPtr>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    
    //pub scheduler: Scheduler,
    pub scheduler: MarsStaticLinkedList<MAX_NUM_THREADS>,
    pub endpoint_ptrs: Ghost<Set<EndpointPtr>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,

    pub pcid_closure : Ghost<Set<Pcid>>,
}

impl Process {
    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub closed spec fn get_pcid(&self) -> Pcid {
        self.pcid
    }
}

impl Thread {
    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

}

impl ProcessManager {

    // pub closed spec fn get_procs(&self) -> Seq<Process>
    // {
    //     Seq::new(self.proc_ptrs@.len(), |i: int| self.proc_perms@[self.proc_ptrs@[i]]@.value.get_Some_0())
    // }

    pub open spec fn get_proc_ptrs(&self) -> Seq<ProcPtr>
    {
        self.proc_ptrs@
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
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  0 <= self.thread_perms@[thread_ptr].view().value.get_Some_0().state <= 4)
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
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == SCHEDULED
            ==> self.scheduler@.contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()) == thread_ptr )
    }
    pub closed spec fn wf_endpoints(&self) -> bool{
        (self.endpoint_ptrs@ =~= self.endpoint_perms@.dom())
        &&
        (self.endpoint_perms@.dom().contains(0) == false)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.is_Some())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().pptr == endpoint_ptr)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.wf())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.unique())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
            ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.len() == self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
            ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
                ==> (
                    self.thread_perms@.dom().contains(thread_ptr)
                    &&
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().state == BLOCKED
                    &&
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() == endpoint_ptr
                )
        ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors.wf())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
            ==> (forall|i:int,j:int| #![auto] i != j && 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && 0<=j<MAX_NUM_ENDPOINT_DESCRIPTORS 
                ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[i] == 0 || 
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[j] == 0 || 
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[i] != self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[j]
                )
            )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
            ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
                ==> self.endpoint_perms@.dom().contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i])
            ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
            ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
                ==> self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i]]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
            ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() != 0)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_rf.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue@.contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap())
        )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap()) == thread_ptr
        )
    }

    closed spec fn local_page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        self.local_page_closure()
        +
        self.proc_ptrs@.to_set()
        +
        self.get_thread_ptrs()
        // self.proc_ptrs@.fold_left(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: ProcPtr| -> Set::<PagePtr> {
        //         acc + self.proc_perms@[e]@.value.get_Some_0().page_closure()
        // })
        // +
        // self.get_thread_ptrs().fold(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: ThreadPtr| -> Set::<PagePtr> {
        //         acc + self.thread_perms@[e]@.value.get_Some_0().page_closure()
        // })
        // + ... fold page closures of other PM components
    }

    pub closed spec fn pcid_closure(&self) -> Set<Pcid>
    {
        self.pcid_closure@
    }

    ///Memory spec helper
    ///specs:
    ///For two different Processes, their page closures are disjoint.
    ///For any process, its data closure is disjoint with any page closure of the system.
    pub closed spec fn wf_mem_closure(&self) -> bool{
        (self.proc_ptrs@.to_set().disjoint(self.get_thread_ptrs()))


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
            self.pcid_closure().finite()
        )
        &&
        (
            forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
                ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_pcid() != self.proc_perms@[proc_ptr_j].view().value.get_Some_0().get_pcid()
        )
        &&
        (
            forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr)
                ==>  self.pcid_closure().contains(self.proc_perms@[proc_ptr].view().value.get_Some_0().get_pcid())
        )
        &&
        (
            self.proc_ptrs@.len() == self.pcid_closure().len()
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
        &&
        self.wf_endpoints()
    }

    pub fn push_scheduler(&mut self, thread_ptr: ThreadPtr)
        requires 
            old(self).wf(),
            old(self).scheduler.len() < MAX_NUM_THREADS,
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state != SCHEDULED,
            old(self).get_thread(thread_ptr).state != BLOCKED,
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
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(ret));
        thread_set_state(&thread_pptr,&mut thread_perm, SCHEDULED);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
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
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.get_thread(ret).state == TRANSIT,
            self.get_thread(ret).parent == old(self).get_thread(ret).parent,
            //self.get_thread(ret).state == old(self).get_thread(ret).state,
            self.get_thread(ret).parent_rf == old(self).get_thread(ret).parent_rf,
            self.get_thread(ret).scheduler_rf == old(self).get_thread(ret).scheduler_rf,
            self.get_thread(ret).endpoint_rf == old(self).get_thread(ret).endpoint_rf,
            self.get_thread(ret).endpoint_descriptors == old(self).get_thread(ret).endpoint_descriptors,
            self.get_thread(ret).parent_rf == old(self).get_thread(ret).parent_rf,
    {
        let ret = self.scheduler.pop();
        let thread_pptr = PPtr::<Thread>::from_usize(ret);
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(ret));
        thread_set_state(&thread_pptr, &mut thread_perm, TRANSIT);
        proof{
            assert(self.thread_perms@.dom().contains(ret) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(ret, thread_perm.get());
        }
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
            old(self).get_thread(thread_ptr).state != BLOCKED,
            old(self).scheduler@.contains(thread_ptr) == false,
            0<=state<=3,
            state != SCHEDULED,
            state != BLOCKED,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.get_thread(thread_ptr).state == state,
    {
        let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        thread_set_state(&thread_pptr, &mut thread_perm, state);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
        }
        assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
            ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr) == false);
        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
    }

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
            self.pcid_closure() =~= old(self).pcid_closure().insert(new_pcid),
    {
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

        //assert()

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

    pub fn new_thread(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, parent_ptr:ProcPtr) -> (ret: ProcPtr)
        requires
            old(self).wf(),
            old(self).get_proc_ptrs().contains(parent_ptr),
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).scheduler.len() < MAX_NUM_THREADS,
            old(self).proc_perms@[parent_ptr]@.value.get_Some_0().owned_threads.len()<MAX_NUM_THREADS_PER_PROC,
        ensures
            self.wf(),
    {
        assert(self.thread_ptrs@.contains(page_ptr) == false);
        assert(forall|_proc_ptr: usize| #![auto] self.proc_perms@.dom().contains(_proc_ptr) ==> self.proc_perms@[_proc_ptr]@.value.get_Some_0().owned_threads@.contains(page_ptr) == false);

        let (thread_pptr,mut thread_perm) = page_to_thread((PPtr::<[u8; PAGE_SIZE]>::from_usize(page_ptr),page_perm));
        thread_set_state(&thread_pptr, &mut thread_perm, SCHEDULED);
        let scheduler_rf = self.scheduler.push(page_ptr);
        thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(scheduler_rf));
        thread_set_parent(&thread_pptr, &mut thread_perm,parent_ptr);

        assert(self.proc_perms@.dom().contains(parent_ptr));
        let mut proc_perm =
            Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));
        
        let parent_rf = proc_push_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, page_ptr);
        assert(self.proc_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(parent_ptr, proc_perm.get());
        }
        thread_set_parent_rf(&thread_pptr, &mut thread_perm,parent_rf);
        assert(self.thread_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.thread_perms.borrow_mut())
                .tracked_insert(page_ptr, thread_perm.get());
        }
        proof{
            self.thread_ptrs@ = self.thread_ptrs@.insert(page_ptr);
        }
        assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
            ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(page_ptr) == false);
        assert(self.wf());
        return page_ptr;
    }

    pub fn free_thread_from_scheduler(&mut self, thread_ptr:ThreadPtr)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == SCHEDULED,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let parent_ptr = thread.parent;
        assert(self.get_proc_ptrs().contains(parent_ptr));
        assert(self.proc_perms@.dom().contains(parent_ptr));
        assert(self.get_proc(parent_ptr).owned_threads.wf());
        assert(self.get_proc(parent_ptr).owned_threads@.contains(thread_ptr));
        assert(self.scheduler.wf());
        assert(self.scheduler@.contains(thread_ptr));
        assert(thread.scheduler_rf.is_Some());
        self.scheduler.remove(thread.scheduler_rf.unwrap());
        assert(self.scheduler@.contains(thread_ptr) == false);

        assert(self.proc_perms@.dom().contains(parent_ptr));
        let mut proc_perm =
            Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));
        proc_remove_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, thread.parent_rf);
        assert(self.proc_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(parent_ptr, proc_perm.get());
        }
        proof{
            (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr);
        }
        proof{
            self.thread_ptrs@ = self.thread_ptrs@.remove(thread_ptr);
        }
        assert(self.wf());
    }
    pub fn free_thread_from_endpoint(&mut self, thread_ptr:ThreadPtr)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == BLOCKED,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let parent_ptr = thread.parent;
        assert(self.get_proc_ptrs().contains(parent_ptr));
        assert(self.proc_perms@.dom().contains(parent_ptr));
        assert(self.get_proc(parent_ptr).owned_threads.wf());
        assert(self.get_proc(parent_ptr).owned_threads@.contains(thread_ptr));

        assert(thread.endpoint_rf.is_Some());
        assert(thread.endpoint_ptr.is_Some());

        assert(self.proc_perms@.dom().contains(parent_ptr));
        let mut proc_perm =
            Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));
        proc_remove_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, thread.parent_rf);
        assert(self.proc_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(parent_ptr, proc_perm.get());
        }

        let endpoint_ptr = thread.endpoint_ptr.unwrap();
        let endpoint_rf = thread.endpoint_rf.unwrap();

        assert(thread.endpoint_descriptors@.contains(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let mut endpoint_perm =
            Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(endpoint_perm@@.value.get_Some_0().queue@.contains(thread_ptr));
        endpoint_remove_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, endpoint_rf);
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        proof{
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        proof{
            (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr);
        }
        proof{
            self.thread_ptrs@ = self.thread_ptrs@.remove(thread_ptr);
        }

        assert(self.wf());
    }
}
}