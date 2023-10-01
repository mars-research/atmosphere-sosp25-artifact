use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SIZE,
};

use crate::linked_list::*;
use crate::page::{PagePtr,Pcid,PagePPtr,PagePerm};
use crate::pcid_alloc::PCID_MAX;
use crate::sched::{Scheduler, Endpoint};
use crate::mars_array::MarsArray;
use crate::mars_staticlinkedlist::*;

verus! {
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
    pub pl_rf: Index,
    pub pcid: Pcid,
    pub owned_threads: MarsStaticLinkedList<MAX_NUM_THREADS_PER_PROC>,
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

    pub pcid_closure : Ghost<Set<Pcid>>,
}
    //TODO: @Xiangdong Send all these seters to a different file and @Zhaofeng can write same macro.
    #[verifier(external_body)]
    pub fn page_to_proc(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Process>, Tracked<PointsTo<Process>>))
        requires page.0.id() == page.1@@.pptr,
                page.1@@.value.is_Some(),
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == page.0.id(),
                ret.1@@.value.is_Some(),
                ret.1@@.value.get_Some_0().owned_threads.arr_seq@.len() == MAX_NUM_THREADS_PER_PROC,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub fn page_to_thread(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Thread>, Tracked<PointsTo<Thread>>))
        requires page.0.id() == page.1@@.pptr,
                page.1@@.value.is_Some(),
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == page.0.id(),
                ret.1@@.value.is_Some(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub fn proc_to_page(proc: (PPtr::<Process>, Tracked<PointsTo<Process>>)) -> (ret :(PagePPtr,Tracked<PagePerm>))
        requires proc.0.id() == proc.1@@.pptr,
                 proc.1@@.value.is_Some(),
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == proc.0.id(),
                ret.1@@.value.is_Some(),
    {
        unimplemented!();
    }
    
    #[verifier(external_body)]
    pub fn proc_perm_init(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>)
        requires 
            proc_pptr.id() == old(proc_perm)@@.pptr,
            old(proc_perm)@@.value.is_Some(),
            old(proc_perm)@@.value.get_Some_0().owned_threads.arr_seq@.len() == MAX_NUM_THREADS_PER_PROC,
        ensures
            proc_pptr.id() == proc_perm@@.pptr,
            proc_perm@@.value.is_Some(),
            proc_perm@@.value.get_Some_0().owned_threads.wf(),
            proc_perm@@.value.get_Some_0().owned_threads@ =~= Seq::empty(),
    {
        let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
        (*uptr).assume_init_mut().owned_threads.init();
    }

    #[verifier(external_body)]
    pub fn proc_set_pl_rf(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>, pl_rf: Index)
        requires 
            proc_pptr.id() == old(proc_perm)@@.pptr,
            old(proc_perm)@@.value.is_Some(),
            old(proc_perm)@@.value.get_Some_0().owned_threads.wf(),
        ensures
            proc_pptr.id() == proc_perm@@.pptr,
            proc_perm@@.value.is_Some(),
            //proc_perm@@.value.get_Some_0().owned_threads.wf(),
            proc_perm@@.value.get_Some_0().owned_threads =~= old(proc_perm)@@.value.get_Some_0().owned_threads,
            //proc_perm@@.value.get_Some_0().pl_rf =~= old(proc_perm)@@.value.get_Some_0().pl_rf,
            proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
            proc_perm@@.value.get_Some_0().pl_rf =~= pl_rf,
    {
        let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
        (*uptr).assume_init_mut().pl_rf = pl_rf;
    }

    #[verifier(external_body)]
    pub fn proc_set_pcid(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>, pcid: Pcid)
        requires 
            proc_pptr.id() == old(proc_perm)@@.pptr,
            old(proc_perm)@@.value.is_Some(),
            old(proc_perm)@@.value.get_Some_0().owned_threads.wf(),
        ensures
            proc_pptr.id() == proc_perm@@.pptr,
            proc_perm@@.value.is_Some(),
            //proc_perm@@.value.get_Some_0().owned_threads.wf(),
            proc_perm@@.value.get_Some_0().owned_threads =~= old(proc_perm)@@.value.get_Some_0().owned_threads,
            proc_perm@@.value.get_Some_0().pl_rf =~= old(proc_perm)@@.value.get_Some_0().pl_rf,
            //proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
            proc_perm@@.value.get_Some_0().pcid =~= pcid,
    {
        let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
        (*uptr).assume_init_mut().pcid = pcid;
    }

    #[verifier(external_body)]
    pub fn proc_push_thread(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>, thread_ptr: ThreadPtr) -> (free_node_index: Index)
        requires 
            proc_pptr.id() == old(proc_perm)@@.pptr,
            old(proc_perm)@@.value.is_Some(),
            old(proc_perm)@@.value.get_Some_0().owned_threads.wf(),
            old(proc_perm)@@.value.get_Some_0().owned_threads@.contains(thread_ptr) == false,
            old(proc_perm)@@.value.get_Some_0().owned_threads.len()<MAX_NUM_THREADS_PER_PROC,
        ensures
            proc_pptr.id() == proc_perm@@.pptr,
            proc_perm@@.value.is_Some(),
            proc_perm@@.value.get_Some_0().owned_threads.wf(),
            //proc_perm@@.value.get_Some_0().owned_threads =~= old(proc_perm)@@.value.get_Some_0().owned_threads,
            proc_perm@@.value.get_Some_0().pl_rf =~= old(proc_perm)@@.value.get_Some_0().pl_rf,
            proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
            proc_perm@@.value.get_Some_0().owned_threads@ == old(proc_perm)@@.value.get_Some_0().owned_threads@.push(thread_ptr),
            proc_perm@@.value.get_Some_0().owned_threads.value_list@ == old(proc_perm)@@.value.get_Some_0().owned_threads.value_list@.push(free_node_index),
            proc_perm@@.value.get_Some_0().owned_threads.len() == old(proc_perm)@@.value.get_Some_0().owned_threads.len() + 1,
            proc_perm@@.value.get_Some_0().owned_threads.arr_seq@[free_node_index as int].value == thread_ptr,
            proc_perm@@.value.get_Some_0().owned_threads.node_ref_valid(free_node_index),
            proc_perm@@.value.get_Some_0().owned_threads.node_ref_resolve(free_node_index) == thread_ptr,
            forall|index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(index) ==> proc_perm@@.value.get_Some_0().owned_threads.node_ref_valid(index),
            forall|index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(index) ==> index != free_node_index,
            forall|index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(index) ==> old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(index) ==  proc_perm@@.value.get_Some_0().owned_threads.node_ref_resolve(index),
            proc_perm@@.value.get_Some_0().owned_threads.unique(),
            forall| ptr: usize| ptr != thread_ptr ==> old(proc_perm)@@.value.get_Some_0().owned_threads@.contains(ptr) ==  proc_perm@@.value.get_Some_0().owned_threads@.contains(ptr),
            proc_perm@@.value.get_Some_0().owned_threads@.contains(thread_ptr),
    {
        let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
        return (*uptr).assume_init_mut().owned_threads.push(thread_ptr);
    }


#[verifier(external_body)]
pub fn thread_set_scheduler_rf(pptr: &PPtr::<Thread>, perm: &mut Tracked< PointsTo<Thread>>, scheduler_rf: Option<Index>)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
            perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
            perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
            //perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
            perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
            perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
            perm@@.value.get_Some_0().scheduler_rf == scheduler_rf,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().scheduler_rf = scheduler_rf;
    }
}

#[verifier(external_body)]
pub fn thread_set_state(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, state: ThreadState)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
            //perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
            perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
            perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
            perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
            perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
            perm@@.value.get_Some_0().state == state,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().state = state;
    }
}

#[verifier(external_body)]
pub fn thread_set_parent(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent: ProcPtr)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            //perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
            perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
            perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
            perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
            perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
            perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
            perm@@.value.get_Some_0().parent == parent,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().parent = parent;
    }
}


#[verifier(external_body)]
pub fn thread_set_parent_rf(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent_rf: Index)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
            perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
            //perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
            perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
            perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
            perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
            perm@@.value.get_Some_0().parent_rf == parent_rf,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().parent_rf =parent_rf;
    }
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
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        thread_set_state(&thread_pptr, &mut thread_perm, state);
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
        assert(self.wf());
        return page_ptr;
    }
}
}