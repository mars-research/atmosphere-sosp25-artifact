use vstd::prelude::*;
use vstd::ptr::PointsTo;
use vstd::ptr::PPtr;

use crate::linked_list::*;
use crate::page::{PagePPtr,VAddr,PAddr,Pcid};
use crate::paging::AddressSpace;

pub type ThreadPtr = usize;
pub type ProcPtr = usize;

pub struct Process{
    pub owned_threads: LinkedList<ThreadPtr>,

    pub pcid: Pcid,
    pub page_table_pptr: PPtr<AddressSpace>,
    pub page_table_perm: Option<PointsTo<AddressSpace>>,
    //pub page_closure:  Ghost<Set<PagePPtr>>, //all the pages used by maintaining the struct of this process, including its threads'
    //pub data_page_closure: Ghost<Set<PagePPtr>>, // all the data page this process has access to. 
}

pub struct Thread{
    pub parent: ProcPtr,
    pub parent_linkedlist_ptr: NodeRef<ThreadPtr>,
}

///TODO: @Xiangdong think about where to put scheduler and endpoints
pub struct ProcessManager{
    pub proc_ptrs: LinkedList<ProcPtr>,
    pub proc_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,

    pub thread_ptrs: LinkedList<ThreadPtr>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    
    // pub scheduler: LinkedList<ThreadPtr>,

    // pub page_closure_local:  Ghost<Set<PagePPtr>>, //all the pages that this PM has

    //pub page_closure:  Ghost<Set<PagePPtr>>, //all the pages of proc, thread, scheduler, endpoints
    // pub data_page_closure: Ghost<Set<PagePPtr>>, // all the data page of all the processes
}
verus! {

impl Process {
    pub closed spec fn page_closure(&self) -> Set<PagePPtr>
    {
        self.page_table_perm.unwrap()@.value.get_Some_0().0.tmp_table_page_closure()
    }

    pub closed spec fn data_page_closure(&self) -> Set<PagePPtr>
    {
        self.page_table_perm.unwrap()@.value.get_Some_0().0.tmp_data_page_closure()
    }

    pub closed spec fn va2pa_mapping(&self) -> Map<VAddr,PAddr>
    {
        self.page_table_perm.unwrap()@.value.get_Some_0().0.tmp_va2pa_mapping()
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

    pub closed spec fn data_page_closure(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }
}

impl ProcessManager {

    pub closed spec fn get_procs(&self) -> Seq<Process>
    {
        Seq::new(self.proc_ptrs@.len(), |i: int| self.proc_perms@[self.proc_ptrs@[i]]@.value.get_Some_0())
    }

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

    ///spec helper for processes
    ///specs: 
    ///Process list (PL) contains no duplicate process pointers
    ///PM contains and only contains process perms of its process pointers
    ///Each process owns contains no duplicate thread pointers
    ///Each process owns a valid reverse pointer to free it from PL
    pub closed spec fn wf_procs(&self) -> bool{
        true
        // (self.proc_ptrs.wf())
        // &&            
        // (self.proc_ptrs.unique())
        // &&
        // (self.proc_ptrs@.to_set() =~= self.proc_perms@.dom())
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.is_Some())
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().pptr == proc_ptr)
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.wf())
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.unique())
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_valid(&self.proc_perms@[i].view().value.get_Some_0().needle))
        // &&
        // (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_resolve(&self.proc_perms@[i].view().value.get_Some_0().needle) == i)
    }

    ///spec helper for threads
    ///specs: 
    ///Thread list (TL) contains no duplicate thread pointers
    ///PM contains and only contains thread perms of its thread pointers
    ///Each thread has a parent which owns this thread in its owned_threads list
    ///Each process owns a valid reverse pointer to free it from its parent process's owned_threads list
    ///Each process owns a valid reverse pointer to free it from the scheduler
    ///Each process owns a valid reverse pointer to free it from the endpoints
    pub closed spec fn wf_threads(&self) -> bool{
        true
        // (self.thread_ptrs.wf())
        // &&   
        // (self.thread_ptrs.unique())
        // &&
        // (self.thread_ptrs@.to_set() =~= self.thread_perms@.dom())
        // &&
        // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.is_Some())
        // &&
        // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().pptr == thread_ptr)
        // && 
        // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_ptrs@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent))
        // && 
        // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(thread_ptr))
        // && 
        // (forall|proc_ptr: ProcPtr, thread_ptr: ThreadPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
        //     ==>  self.thread_perms@.dom().contains(thread_ptr))
        // && 
        // (forall|proc_ptr: usize, thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
        //         ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().parent == proc_ptr)
        // // && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
        // //   self.proc_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_valid(&self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_needle)  == true)
        // // && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
        // //     self.proc_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_resolve(&self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_needle) == thread_ptr)            && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
        // //     self.thread_ptrs.needle_valid(&self.thread_perms@[thread_ptr].view().value.get_Some_0().needle) == true)
        // // && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
        // //     self.thread_ptrs.needle_resolve(&self.thread_perms@[thread_ptr].view().value.get_Some_0().needle) == thread_ptr)
        // // && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduled == true ==>
        // //     self.scheduler.needle_valid(&self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_needle) == true)
        // // && 
        // // (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduled == true ==>
        // //     self.scheduler.needle_resolve(&self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_needle) == thread_ptr)
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
        self.thread_ptrs@.fold_left(Set::<PagePPtr>::empty(), |acc: Set::<PagePPtr>, e: ThreadPtr| -> Set::<PagePPtr> {
                acc + self.thread_perms@[e]@.value.get_Some_0().page_closure()
        })
        // + ... fold page closures of other PM components
    }

    pub closed spec fn data_page_closure(&self) -> Set<PagePPtr>
    {
        self.proc_ptrs@.fold_left(Set::<PagePPtr>::empty(), |acc: Set::<PagePPtr>, e: ProcPtr| -> Set::<PagePPtr> {
            acc + self.proc_perms@[e]@.value.get_Some_0().data_page_closure()
        })
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
        self.wf_mem_closure()
        &&
        self.wf_pcid_closure()
    }

}
}