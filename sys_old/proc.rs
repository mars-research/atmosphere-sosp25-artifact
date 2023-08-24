

use super::*;

pub const NUM_PROCESS: usize = 2;
pub const THREAD_PRE_PROC: usize = 2;
pub const NUM_THREAD: usize = NUM_PROCESS * 4;
pub type ProcID = usize;
pub type ThreadID = usize;
pub type ProcPtr = usize;
pub type ThreadPtr = usize;


verus! {
    #[verifier(external_body)]
    proof fn lemma_same_raw_ptr(ptr1 :int, ptr2 :int)
        ensures
            ptr1 == ptr2,
    {
        unimplemented!();
    }


    pub struct Process{
        pub owned_threads: MarsStaticLinkedList<THREAD_PRE_PROC>,
        //pub PID: ProcID,
        //pub num_threads: usize,
        pub is_free: bool,
    }

    pub struct Thread{
        //pub TID: ThreadID,
        pub parent: ProcPtr,
        pub is_free: bool,
        pub parent_node_index: isize,
        pub scheduled: bool,
        pub scheduler_node_index: isize,
    }
    
    pub struct ProcessManager{
        pub free_proc_ptrs: MarsStaticLinkedList<NUM_PROCESS>,
        //pub process_table: MarsArray<ProcPtr,NUM_PROCESS>,
        pub proc_perms: Tracked<Map<int, PointsTo<Process>>>,
        //pub free_proc_count: usize,

        pub free_thread_ptrs: MarsStaticLinkedList<NUM_THREAD>,
        //pub thread_table: MarsArray<ThreadPtr,NUM_THREAD>,
        pub thread_perms: Tracked<Map<int, PointsTo<Thread>>>,
        //pub free_thread_count: usize,
        
        pub scheduler: MarsStaticLinkedList<NUM_THREAD>,
    }

    impl ProcessManager {

        fn update_proc_is_free(&mut self, proc_ptr: ProcPtr, is_free: bool)
        requires
                old(self).proc_perms@.dom().contains(proc_ptr as int),
                old(self).wf_proc_perms(),
        ensures self.scheduler == old(self).scheduler,
                self.thread_perms == old(self).thread_perms,
                self.free_thread_ptrs == old(self).free_thread_ptrs,
                self.free_proc_ptrs == old(self).free_proc_ptrs,
                self.proc_perms@.dom() == old(self).proc_perms@.dom(),
                forall |_proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && _proc_ptr != proc_ptr 
                    ==> self.proc_perms@[_proc_ptr as int] == old(self).proc_perms@[_proc_ptr as int],
                self.proc_perms@[proc_ptr as int].view().value.is_Some(),
                self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr,
                self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads,
                self.proc_perms@[proc_ptr as int].view().value.get_Some_0().is_free == is_free,

    {
        let proc_pptr = PPtr::<Process>::from_usize(proc_ptr as usize);
        assert(self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr as int);
        let tracked mut proc_perm: PointsTo<Process> =
            (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr as int);
        assert(proc_perm@.pptr == proc_ptr as int);
        assert(proc_ptr as int == proc_pptr.id());
        let mut proc = proc_pptr.take(Tracked(&mut proc_perm));
        proc.is_free = is_free;
        let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
        proof {
            lemma_same_raw_ptr(new_proc_pptr.id(), proc_ptr as int);
            (self.proc_perms.borrow_mut())
                .tracked_insert(proc_ptr as int, (new_proc_perm).get());
        }       
        assert(self.proc_perms@.dom().ext_equal(old(self).proc_perms@.dom()));   
    }

//     fn push_proc_owned_threads(&mut self, proc_ptr: ProcPtr, thread_ptr: ThreadPtr) -> (node_index: isize)
//         requires
//                 old(self).proc_perms@.dom().contains(proc_ptr as int),
//                 old(self).wf_proc_perms(),
//                 old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.wf(),
//                 old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() < THREAD_PRE_PROC,
//                 old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.is_unique(),
//                 old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false,
//         ensures self.scheduler == old(self).scheduler,
//                 self.thread_perms == old(self).thread_perms,
//                 self.free_thread_ptrs == old(self).free_thread_ptrs,
//                 self.free_proc_ptrs == old(self).free_proc_ptrs,
//                 self.proc_perms@.dom() == old(self).proc_perms@.dom(),
//                 forall |_proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && _proc_ptr != proc_ptr 
//                     ==> self.proc_perms@[_proc_ptr as int] == old(self).proc_perms@[_proc_ptr as int],
//                 self.proc_perms@[proc_ptr as int].view().value.is_Some(),
//                 self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr,
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().is_free == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().is_free,
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@ == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.push(thread_ptr),
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() + 1,
//                 //self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.spec_seq@ == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.spec_seq@.push(thread_ptr),
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@ == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.push(node_index),
//                 //self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.arr_seq@[node_index as int].ptr == thread_ptr,
//                 0 <= node_index < THREAD_PRE_PROC,
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.is_unique(),
//                 forall| ptr: ThreadPtr| ptr != thread_ptr ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.spec_seq@.contains(ptr) == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.spec_seq@.contains(ptr),
//                 self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.spec_seq@.contains(thread_ptr),

//     {
//         let proc_pptr = PPtr::<Process>::from_usize(proc_ptr as usize);
//         assert(self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr as int);
//         let proc_perm: Tracked<PointsTo<Process>> = tracked(
//             (tracked self.proc_perms.borrow_mut()).tracked_remove(proc_ptr as int));
//         assert(proc_perm@@.pptr == proc_ptr as int);
//         assert(proc_ptr as int == proc_pptr.id());
//         let mut proc = proc_pptr.into_inner(proc_perm); 
//         let node_index = proc.owned_threads.push(thread_ptr);
//         let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
//         proof {
//             lemma_same_raw_ptr(new_proc_pptr.id(), proc_ptr as int);
//             (tracked self.proc_perms.borrow_mut())
//                 .tracked_insert(proc_ptr as int, (tracked new_proc_perm).get());
//         }       
//         assert(self.proc_perms@.dom().ext_equal(old(self).proc_perms@.dom()));   
//         return node_index;
//     }

//     fn update_thread_is_free(&mut self, thread_ptr: ThreadPtr, is_free: bool)
//     requires
//             old(self).thread_perms@.dom().contains(thread_ptr as int),
//             old(self).wf_thread_perms(),
//     ensures self.scheduler == old(self).scheduler,
//             self.proc_perms == old(self).proc_perms,
//             self.free_thread_ptrs == old(self).free_thread_ptrs,
//             self.free_proc_ptrs == old(self).free_proc_ptrs,
//             self.thread_perms@.dom() == old(self).thread_perms@.dom(),
//             forall |_thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr as int) && _thread_ptr != thread_ptr 
//                 ==> self.thread_perms@[_thread_ptr as int] == old(self).thread_perms@[_thread_ptr as int],
//             self.thread_perms@[thread_ptr as int].view().value.is_Some(),
//             self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr,
//             self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent,
//             self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent_node_index == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent_node_index,
//             self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled,
//             self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index,
//             self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == is_free,

// {
//             let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
//             assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
//             let thread_perm: Tracked<PointsTo<Thread>> = tracked(
//                 (tracked self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int));
//             assert(thread_perm@@.pptr == thread_ptr as int);
//             assert(thread_ptr as int == thread_pptr.id());
//             let mut thread = thread_pptr.into_inner(thread_perm); 
//             thread.is_free = is_free;

//             let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
//             proof {
//                 lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
//                 (tracked self.thread_perms.borrow_mut())
//                     .tracked_insert(thread_ptr as int, (tracked new_thread_perm).get());
//             } 
//             assert(self.thread_perms@.dom().ext_equal(old(self).thread_perms@.dom()));  
// }


// fn update_thread_parent(&mut self, thread_ptr: ThreadPtr, new_parent: ProcPtr)
//     requires
//         old(self).thread_perms@.dom().contains(thread_ptr as int),
//         old(self).wf_thread_perms(),
//     ensures self.scheduler == old(self).scheduler,
//         self.proc_perms == old(self).proc_perms,
//         self.free_thread_ptrs == old(self).free_thread_ptrs,
//         self.free_proc_ptrs == old(self).free_proc_ptrs,
//         self.thread_perms@.dom() == old(self).thread_perms@.dom(),
//         forall |_thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr as int) && _thread_ptr != thread_ptr 
//             ==> self.thread_perms@[_thread_ptr as int] == old(self).thread_perms@[_thread_ptr as int],
//         self.thread_perms@[thread_ptr as int].view().value.is_Some(),
//         self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent_node_index == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent_node_index,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == new_parent,

//     {
//         let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
//         assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
//         let thread_perm: Tracked<PointsTo<Thread>> = tracked(
//             (tracked self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int));
//         assert(thread_perm@@.pptr == thread_ptr as int);
//         assert(thread_ptr as int == thread_pptr.id());
//         let mut thread = thread_pptr.into_inner(thread_perm); 
//         thread.parent = new_parent;

//         let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
//         proof {
//             lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
//             (tracked self.thread_perms.borrow_mut())
//                 .tracked_insert(thread_ptr as int, (tracked new_thread_perm).get());
//         } 
//         assert(self.thread_perms@.dom().ext_equal(old(self).thread_perms@.dom()));  
//     }

//     fn update_thread_parent_node_index(&mut self, thread_ptr: ThreadPtr, parent_node_index: isize)
//     requires
//         old(self).thread_perms@.dom().contains(thread_ptr as int),
//         old(self).wf_thread_perms(),
//     ensures self.scheduler == old(self).scheduler,
//         self.proc_perms == old(self).proc_perms,
//         self.free_thread_ptrs == old(self).free_thread_ptrs,
//         self.free_proc_ptrs == old(self).free_proc_ptrs,
//         self.thread_perms@.dom() == old(self).thread_perms@.dom(),
//         forall |_thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr as int) && _thread_ptr != thread_ptr 
//             ==> self.thread_perms@[_thread_ptr as int] == old(self).thread_perms@[_thread_ptr as int],
//         self.thread_perms@[thread_ptr as int].view().value.is_Some(),
//         self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index == old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduler_node_index,
//         self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent_node_index == parent_node_index,

//     {
//         let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
//         assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
//         let thread_perm: Tracked<PointsTo<Thread>> = tracked(
//             (tracked self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int));
//         assert(thread_perm@@.pptr == thread_ptr as int);
//         assert(thread_ptr as int == thread_pptr.id());
//         let mut thread = thread_pptr.into_inner(thread_perm); 
//         thread.parent_node_index = parent_node_index;

//         let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
//         proof {
//             lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
//             (tracked self.thread_perms.borrow_mut())
//                 .tracked_insert(thread_ptr as int, (tracked new_thread_perm).get());
//         } 
//         assert(self.thread_perms@.dom().ext_equal(old(self).thread_perms@.dom()));  
//     }

        pub open spec fn wf_proc_perms(&self) -> bool{
            forall|i: ProcPtr| #![auto] self.proc_perms@.dom().contains(i as int) ==> 
            (
                (self.proc_perms@[i as int].view().pptr == i)
                &&
                (self.proc_perms@[i as int].view().value.is_Some())
                &&
                (i != 0)
                // &&
                // (self.process_table@.contains(i))
                &&
                (
                    self.proc_perms@[i as int].view().value.get_Some_0().is_free ==> self.proc_perms@[i as int].view().value.get_Some_0().owned_threads@.len() == 0
                )
            )
        }
        // pub open spec fn wf_process_table(&self) -> bool{
        //     (
        //         self.process_table.wf()
        //     )
        //     &&
        //     (
        //         forall|i:int, j:int|#![auto] 0 <= i < NUM_PROCESS && 0 <= j < NUM_PROCESS && i != j 
        //             ==> self.process_table[i] != self.process_table[j]
        //     )
        //     &&
        //     (
        //         forall|i:int|#![auto] 0 <= i < NUM_PROCESS 
        //             ==> self.proc_perms@.dom().contains(self.process_table[i] as int)
        //     )
        //     &&
        //     (
        //         forall|i: int| #![auto] self.proc_perms@.dom().contains(i)                  
        //             ==> 
        //             (
        //                 self.process_table[self.proc_perms@[i].view().value.get_Some_0().PID as int] as int == i
        //             )
        //             &&
        //             (
        //                 0 <= self.proc_perms@[i].view().value.get_Some_0().PID < NUM_PROCESS
        //             )
        //     )
        // }
        
        pub open spec fn wf_free_proc_ptrs(&self) -> bool{
            self.free_proc_ptrs.wf()
            &&
            (
                self.free_proc_ptrs.is_unique()
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_proc_ptrs@.len()                     
                    ==> (
                            self.proc_perms@.dom().contains(self.free_proc_ptrs@[i] as int)
                        )
            )
            // &&
            // (
            //     self.free_proc_count == self.free_proc_ptrs.pointer_list_len
            // )            
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_proc_ptrs@.len()                     
                    ==> (
                        self.proc_perms@[self.free_proc_ptrs@[i] as int].view().value.get_Some_0().is_free == true
                        )
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_proc_ptrs@.len()                     
                    ==> (
                        self.proc_perms@[self.free_proc_ptrs@[i] as int].view().value.get_Some_0().owned_threads.len() == 0
                        )
            )
        }

        pub open spec fn wf_free_proc(&self) -> bool{
            self.wf_free_proc_ptrs()
            // &&
            // self.wf_process_table()
            &&
            self.wf_proc_perms()
        }

        pub open spec fn wf_thread_perms(&self) -> bool{
            forall|i: ThreadPtr| #![auto] self.thread_perms@.dom().contains(i as int) ==> 
            (
                (self.thread_perms@[i as int].view().pptr == i)
                &&
                (self.thread_perms@[i as int].view().value.is_Some())
                &&
                (i != 0)
                // &&
                // (self.thread_table@.contains(i))
                // &&
                // (self.thread_perms@[i].view().value.get_Some_0().owned_threads@.finite() == true)
            )
        }
        // pub open spec fn wf_thread_table(&self) -> bool{
        //     (
        //         self.thread_table.wf()
        //     )
        //     &&
        //     (
        //         self.thread_table.is_unique()
        //     )
        //     &&
        //     (
        //         forall|i:int|#![auto] 0 <= i < NUM_THREAD 
        //             ==> self.thread_perms@.dom().contains(self.thread_table[i] as int)
        //     )
        //     &&
        //     (
        //         forall|i: int| #![auto] self.thread_perms@.dom().contains(i)                  
        //             ==> 
        //             (
        //                 self.thread_table[self.thread_perms@[i].view().value.get_Some_0().TID as int] as int == i
        //             )
        //             &&
        //             (
        //                 0 <= self.thread_perms@[i].view().value.get_Some_0().TID < NUM_THREAD
        //             )
        //     )
        // }
        
        pub open spec fn wf_free_thread_ptrs(&self) -> bool{
            self.free_thread_ptrs.wf()
            &&
            (
                self.free_thread_ptrs.is_unique()
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_thread_ptrs@.len()                     
                    ==> (
                            self.thread_perms@.dom().contains(self.free_thread_ptrs@[i] as int)
                        )
            )         
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_thread_ptrs@.len()                     
                    ==> (
                        self.thread_perms@[self.free_thread_ptrs@[i] as int].view().value.get_Some_0().is_free == true
                        )
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_thread_ptrs@.len()                     
                    ==> (
                        self.thread_perms@[self.free_thread_ptrs@[i] as int].view().value.get_Some_0().parent == 0
                        )
            )            
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_thread_ptrs@.len()                     
                    ==> (
                        self.thread_perms@[self.free_thread_ptrs@[i] as int].view().value.get_Some_0().scheduled == false
                        )
            )
        }

        // pub open spec fn spec_get_thread_ptr_from_index(&self, parent: ProcPtr, node_index: int) -> ThreadPtr
        //     recommends self.process_table@.contains(parent),
        //                0<= node_index < THREAD_PRE_PROC,
        // {
        //     self.proc_perms@[parent as int].view().value.get_Some_0().owned_threads.arr_seq@[node_index].ptr
        // }

        pub open spec fn wf_thread_ownership(&self) -> bool{            
            (
                forall|i:ThreadPtr|#![auto] self.thread_perms@.dom().contains(i as int) && self.thread_perms@[i as int].view().value.get_Some_0().is_free != true            
                        ==> self.thread_perms@[i as int].view().value.get_Some_0().parent != 0
            )
            &&
            (
                forall|i:ThreadPtr|#![auto] self.thread_perms@.dom().contains(i as int) && self.thread_perms@[i as int].view().value.get_Some_0().is_free != true            
                        ==> self.proc_perms@.dom().contains(self.thread_perms@[i as int].view().value.get_Some_0().parent as int)
            )
            &&            
            (
                forall|i:ThreadPtr|#![auto] self.thread_perms@.dom().contains(i as int) && self.thread_perms@[i as int].view().value.get_Some_0().is_free != true            
                        ==> 0 <= self.thread_perms@[i as int].view().value.get_Some_0().parent_node_index < THREAD_PRE_PROC
            )
            &&  
            (
                forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                    ==> forall|i: int| #![auto] 0<= i < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len()
                        ==> self.thread_perms@.dom().contains(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int)
            )
            &&
            (
                forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                    ==> forall|i: int| #![auto] 0<= i < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len()
                        ==> self.thread_perms@[self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().is_free != true
            )  
            &&
            (
                forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.wf()
            )
            // TODO: somehow make this fast
            // &&            
            // (
            //     forall|_proc_ptr: ProcPtr, i: int|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && 0 <= i < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len()           
            //             ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@[i] == self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().parent_node_index
            // )
            // &&            
            // (
            //     forall|_proc_ptr: ProcPtr, i: int|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && 0 <= i < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len()           
            //             ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.contains(self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().parent_node_index)
            // )
            // &&            
            // (
            //     forall|_proc_ptr: ProcPtr, i: int, j: int|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && 0 <= i < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len() && 0 <= j < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len() && i != j   
            //             ==> self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().parent_node_index != self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[j] as int].view().value.get_Some_0().parent_node_index
            // )
            &&
            (
                forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.is_unique()
            )
            &&
            (
                forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int)  && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == proc_ptr
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr)
            )            
            &&
            (
                forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int)  && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent != proc_ptr
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false
            )
        }   

        pub open spec fn wf_free_thread(&self) -> bool{
            self.wf_free_thread_ptrs()
            // &&
            // self.wf_thread_table()
            &&
            self.wf_thread_perms()
            // &&
            // self.wf_thread_ownership()
        }      

        pub open spec fn wf_scheduler(&self) -> bool{
            (
                self.scheduler.wf()
            )
            &&
            (
                self.scheduler.is_unique()
            )
            // &&
            // (
            //     forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
            //         ==> self.thread_table@.contains(self.scheduler@[i])
            // )
            &&
            (
                forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
                    ==> self.thread_perms@.dom().contains(self.scheduler@[i] as int)
            )            
            &&
            (
                forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
                    ==> self.thread_perms@[self.scheduler@[i] as int].view().value.get_Some_0().scheduled == true
            )
            &&
            (
                forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
                    ==> self.thread_perms@[self.scheduler@[i] as int].view().value.get_Some_0().is_free == false
            )
            &&
            (
                forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
                    ==> self.thread_perms@[self.scheduler@[i] as int].view().value.get_Some_0().parent != 0
            )
            &&
            (
                forall |i: int|  #![auto] 0<= i < self.scheduler@.len() 
                    ==> self.scheduler.pointer_list@[i] == self.thread_perms@[self.scheduler@[i] as int].view().value.get_Some_0().scheduler_node_index
            )
        }    

        pub fn alloc_process(&mut self) -> (ret : ProcPtr)
            requires 
                old(self).wf_free_proc(),
                old(self).free_proc_ptrs.len() > 0,
                old(self).wf_free_thread(),
                old(self).wf_thread_ownership(),
                old(self).wf_scheduler(),
            ensures
                self.wf_free_proc(),
                self.free_proc_ptrs.len() == old(self).free_proc_ptrs.len() - 1,
                ret != 0,
                self.wf_free_thread(),
                self.wf_thread_ownership(),
                self.wf_scheduler(),
        {
            assert(self.free_proc_ptrs.pointer_list_len > 0);
            let ret = self.free_proc_ptrs.pop();
            assert(self.proc_perms@.dom().contains(ret as int));
            assert(self.proc_perms@[ret as int].view().value.get_Some_0().is_free == true);

            let ret_pptr = PPtr::<Process>::from_usize(ret as usize);
            assert(self.proc_perms@[ret as int].view().pptr == ret as int);
            let tracked mut ret_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(ret as int);
            assert(ret_perm@.pptr == ret as int);
            assert(ret as int == ret_pptr.id());
            let mut proc = ret_pptr.take(Tracked(&mut ret_perm));
            proc.is_free = false;
            let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
            proof {
                lemma_same_raw_ptr(new_proc_pptr.id(), ret as int);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(ret as int, (new_proc_perm).get());
            }          
            // self.free_proc_count = self.free_proc_count - 1;
            assert(self.free_proc_ptrs.wf());
            assert(
                forall|i: int| #![auto] 0 <= i < self.free_proc_ptrs@.len()                     
                    ==> (
                            self.proc_perms@.dom().contains(self.free_proc_ptrs@[i] as int)
                        )
            );
        
            assert(self.wf_free_proc_ptrs());
            //assert(self.wf_process_table());
            assert(self.wf_proc_perms());

            return ret;
        }

        pub fn free_process(&mut self, proc_ptr: ProcPtr)
        requires 
            old(self).wf_free_proc(),
            old(self).free_proc_ptrs.len() < NUM_PROCESS, //this can probaly be infered from the following two specs but too hard to prove it
            //old(self).process_table@.contains(proc_ptr),
            old(self).proc_perms@.dom().contains(proc_ptr as int),
            old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().is_free == false,
            old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() == 0,
            old(self).wf_free_thread(),
            old(self).wf_thread_ownership(),
            old(self).wf_scheduler(),
        ensures
            self.wf_free_proc(),
            self.free_proc_ptrs.len() == old(self).free_proc_ptrs.len() + 1,
            self.wf_free_thread(),
            self.wf_thread_ownership(),
            self.wf_scheduler(),
        {
            assert(self.proc_perms@.dom().contains(proc_ptr as int));
            assert(proc_ptr != 0);
            assert(self.free_proc_ptrs@.contains(proc_ptr) == false);
            assert(old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len() == 0);

            // self.free_proc_count = self.free_proc_count + 1;

            let proc_pptr = PPtr::<Process>::from_usize(proc_ptr as usize);
            assert(self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr as int);
            let tracked mut proc_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr as int);
            assert(proc_perm@.pptr == proc_ptr as int);
            assert(proc_ptr as int == proc_pptr.id());
            let mut proc = proc_pptr.take(Tracked(&mut proc_perm));
            proc.is_free = true;
            let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
            proof {
                lemma_same_raw_ptr(new_proc_pptr.id(), proc_ptr as int);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(proc_ptr as int, (new_proc_perm).get());
            } 

            self.free_proc_ptrs.push(proc_ptr);
            // assert(
            //     forall|i:ThreadPtr|#![auto] self.thread_perms@.dom().contains(i as int) && self.thread_perms@[i as int].view().value.get_Some_0().is_free != true              
            //         ==> self.thread_perms@[i as int].view().value.get_Some_0().parent != 0
            //             &&
            //             self.process_table@.contains(self.thread_perms@[i as int].view().value.get_Some_0().parent) 
            // );
            assert(
                forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.wf()
            );
            assert(
                forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int)  && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == proc_ptr
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr)
            );       
            assert(
                forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int)  && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent != proc_ptr
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false
            );
            //some turing test here 
            //assert(false);
        }
        
        pub fn alloc_thread_to_proc(&mut self, proc_ptr: ProcPtr) -> (thread_ptr: ThreadPtr)
            requires 
                old(self).wf_free_proc(),
                old(self).free_thread_ptrs.len() > 0,
                //old(self).process_table@.contains(proc_ptr),
                old(self).proc_perms@.dom().contains(proc_ptr as int),
                old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().is_free == false,
                old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() < THREAD_PRE_PROC,
                old(self).wf_free_thread(),
                old(self).wf_thread_ownership(),
                old(self).wf_scheduler(),
            ensures
                self.wf_free_proc(),
                self.wf_free_thread(),
                self.wf_thread_ownership(),
                self.wf_scheduler(),
                self.free_thread_ptrs.len() == old(self).free_thread_ptrs.len() - 1,
                self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.len() + 1,
                self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@ == old(self).proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.push(thread_ptr),
        {
            let thread_ptr = self.free_thread_ptrs.pop();

            let proc_pptr = PPtr::<Process>::from_usize(proc_ptr as usize);
            // assert(false);
            assert(self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr as int);
            let tracked mut proc_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr as int);
            assert(proc_perm@.pptr == proc_ptr as int);
            assert(proc_ptr as int == proc_pptr.id());
            let mut proc = proc_pptr.take(Tracked(&mut proc_perm));
            assert(proc.is_free == false);
            assert(self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == 0);
            assert(proc.owned_threads@.contains(thread_ptr) == false);
            let node_index = proc.owned_threads.push(thread_ptr);
            assert(proc.owned_threads@[proc.owned_threads@.len() as int - 1 ] == thread_ptr);
            assert(proc.owned_threads@.contains(thread_ptr));
            // proc.num_threads = proc.num_threads + 1;
            let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
            proof {
                lemma_same_raw_ptr(new_proc_pptr.id(), proc_ptr as int);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(proc_ptr as int, (new_proc_perm).get());
            } 

            let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
            assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
            let tracked mut thread_perm: PointsTo<Thread> =
                (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int);
            assert(thread_perm@.pptr == thread_ptr as int);
            assert(thread_ptr as int == thread_pptr.id());
            let mut thread = thread_pptr.take(Tracked(&mut thread_perm));
            assert(thread.is_free == true);
            assert(thread.parent == 0);
            thread.is_free = false;
            thread.parent = proc_ptr;
            thread.parent_node_index = node_index;

            // self.free_thread_count = self.free_thread_count - 1;
            let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
            proof {
                lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
                (self.thread_perms.borrow_mut())
                    .tracked_insert(thread_ptr as int, (new_thread_perm).get());
            } 
            // assert(
            //     forall|_thread_ptr:ThreadPtr, _proc_ptr: ProcPtr|#![auto] _proc_ptr != proc_ptr && self.thread_perms@.dom().contains(_thread_ptr as int) && self.proc_perms@.dom().contains(_proc_ptr as int) &&  self.thread_perms@[_thread_ptr as int].view().value.get_Some_0().parent == _proc_ptr
            //         ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(_thread_ptr)
            // ); 
            // assert(
            //     forall|_thread_ptr:ThreadPtr, _proc_ptr: ProcPtr|#![auto] _proc_ptr == proc_ptr && self.thread_perms@.dom().contains(_thread_ptr as int) && self.proc_perms@.dom().contains(_proc_ptr as int) &&  self.thread_perms@[_thread_ptr as int].view().value.get_Some_0().parent == _proc_ptr
            //         ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(_thread_ptr)
            // ); 
            // assert(
            //     forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int) &&  self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == proc_ptr
            //         ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr)
            // );           
            // assert(
            //     forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int) && self.proc_perms@.dom().contains(proc_ptr as int)  && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent != proc_ptr
            //         ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false
            // );

            return thread_ptr;
        }
        
        #[verifier(external_body)]
        pub fn check_parent_node_index(&self, proc_ptr:ProcPtr, index: isize, thread_ptr: ThreadPtr)
            ensures 
                self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.arr_seq@[index as int].ptr == thread_ptr,
        {

        }

        pub fn free_thread(&mut self, thread_ptr: ThreadPtr) 
            requires 
                old(self).wf_free_proc(),
                old(self).free_thread_ptrs.len() < NUM_THREAD, // same, can be infered probably, but too hard
                old(self).thread_perms@.dom().contains(thread_ptr as int),
                old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == false,
                old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == false,
                old(self).wf_free_thread(),
                old(self).wf_thread_ownership(),
                old(self).wf_scheduler(),
            ensures
                self.wf_free_proc(),
                self.wf_free_thread(),
                self.wf_thread_ownership(),
                self.wf_scheduler(),
                self.free_thread_ptrs.len() == old(self).free_thread_ptrs.len() + 1,
                self.proc_perms@[old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent as int].view().value.get_Some_0().owned_threads.len() == 
                    old(self).proc_perms@[old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent as int].view().value.get_Some_0().owned_threads.len() - 1,
                self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == true,
                forall|i: ThreadPtr| #![auto] i != thread_ptr ==>
                    old(self).proc_perms@[old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent as int].view().value.get_Some_0().owned_threads@.contains(i) == 
                        self.proc_perms@[old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent as int].view().value.get_Some_0().owned_threads@.contains(i),
                self.proc_perms@[old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().parent as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false,
            {

                let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
                assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
                let tracked mut thread_perm: PointsTo<Thread> =
                    (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int);
                assert(thread_perm@.pptr == thread_ptr as int);
                assert(thread_ptr as int == thread_pptr.id());
                let mut thread = thread_pptr.take(Tracked(&mut thread_perm));
                assert(thread.is_free == false);
                assert(thread.parent != 0);
                thread.is_free = true;

                let proc_ptr = thread.parent;
                thread.parent = 0;
                let index = thread.parent_node_index;
                // thread.parent_node_index = -1;
                self.check_parent_node_index(proc_ptr, index, thread_ptr);

                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.contains(index));
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr));
                let index_in_list:Ghost<int> = Ghost(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.index_of(thread_ptr));
                
                let index_in_pointer_list:Ghost<int> = Ghost(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.index_of(index));
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@[index_in_list@] == thread_ptr);
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.arr_seq@[index as int].ptr == thread_ptr);
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@[index_in_pointer_list@] == index);
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len() <=  THREAD_PRE_PROC);
                assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.wf());
                // assert(0<= index_in_list@ < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len());
                // assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@[index_in_list@] == thread_ptr);
                // assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@[index_in_list@] == index);
                // assert(self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.arr_seq@[index as int].ptr == thread_ptr);

                // self.free_thread_count = self.free_thread_count + 1;
                let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
                proof {
                    lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
                    (self.thread_perms.borrow_mut())
                        .tracked_insert(thread_ptr as int, (new_thread_perm).get());
                } 
                
                let proc_pptr = PPtr::<Process>::from_usize(proc_ptr as usize);
                assert(self.proc_perms@[proc_ptr as int].view().pptr == proc_ptr as int);
                let tracked mut proc_perm: PointsTo<Process> =
                    (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr as int);
                assert(proc_perm@.pptr == proc_ptr as int);
                assert(proc_ptr as int == proc_pptr.id());
                let mut proc = proc_pptr.take(Tracked(&mut proc_perm));
                assert(proc.owned_threads@.contains(thread_ptr));
                assert(proc.owned_threads@.len() > 0);
                assert(proc.is_free == false);
                
                //proc.num_threads = proc.num_threads - 1;
                let removed_ptr = proc.owned_threads.remove(index);
                assert(removed_ptr == thread_ptr);
                // assert(proc.owned_threads.arr_seq@[index as int].ptr == thread_ptr);
                assert(proc.owned_threads@.contains(thread_ptr) == false);
    
                let (new_proc_pptr, new_proc_perm) = PPtr::new(proc);
                proof {
                    lemma_same_raw_ptr(new_proc_pptr.id(), proc_ptr as int);
                    (self.proc_perms.borrow_mut())
                        .tracked_insert(proc_ptr as int, (new_proc_perm).get());
                } 

                self.free_thread_ptrs.push(thread_ptr);
                assert(
                    forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int)   && self.proc_perms@.dom().contains(proc_ptr as int)    && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent == proc_ptr
                        ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr)
                );            
                assert(
                    forall|thread_ptr:ThreadPtr, proc_ptr: ProcPtr|#![auto] self.thread_perms@.dom().contains(thread_ptr as int)   &&  self.proc_perms@.dom().contains(proc_ptr as int)    && self.thread_perms@[thread_ptr as int].view().value.get_Some_0().parent != proc_ptr
                        ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false
                );
                assert(
                    forall|_proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && _proc_ptr != proc_ptr
                        ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@ == old(self).proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@
                );
                assert(
                    forall|_proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && _proc_ptr != proc_ptr
                        ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.contains(thread_ptr) == false );
                assert(
                    forall|_proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(_proc_ptr as int) && _proc_ptr != proc_ptr
                        ==> forall|i: int| #![auto] 0<= i < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len()
                            ==> self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().is_free != true
                );
                assert(
                    forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                        ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.wf()
                );
                assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len() && 0 <= j < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len() 
                    ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@[i as int] != self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@[j as int] );
                
                assert(
                    forall|proc_ptr: ProcPtr|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) 
                        ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.is_unique()
                );

                // assert(
                //     forall|_proc_ptr: ProcPtr, i: int|#![auto] _proc_ptr != proc_ptr && self.proc_perms@.dom().contains(_proc_ptr as int) && 0 <= i < self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@.len()           
                //             ==> self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.contains(self.thread_perms@[self.proc_perms@[_proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().parent_node_index)
                // );

                // assert(
                //     forall| i: int|#![auto] self.proc_perms@.dom().contains(proc_ptr as int) && 0 <= i < self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@.len()           
                //             ==> self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads.pointer_list@.contains(self.thread_perms@[self.proc_perms@[proc_ptr as int].view().value.get_Some_0().owned_threads@[i] as int].view().value.get_Some_0().parent_node_index)
                // );
            }

            pub fn push_schedule_thread(&mut self, thread_ptr: ThreadPtr) 
                requires 
                    old(self).wf_free_proc(),
                    old(self).scheduler.len() < NUM_THREAD, // same, can be infered probably, but too hard
                    old(self).thread_perms@.dom().contains(thread_ptr as int),
                    old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == false,
                    old(self).thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == false,
                    old(self).wf_free_thread(),
                    old(self).wf_thread_ownership(),
                    old(self).wf_scheduler(),
                ensures 
                    self.wf_free_proc(),
                    self.scheduler.len() ==  old(self).scheduler.len() + 1, // same, can be infered probably, but too hard
                    self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == false,
                    self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == true,
                    self.wf_free_thread(),
                    self.wf_thread_ownership(),
                    self.wf_scheduler(),
                    self.scheduler@ == old(self).scheduler@.push(thread_ptr),
            {

                let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
                assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
                let tracked mut thread_perm: PointsTo<Thread> =
                    (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int);
                assert(thread_perm@.pptr == thread_ptr as int);
                assert(thread_ptr as int == thread_pptr.id());
                let mut thread = thread_pptr.take(Tracked(&mut thread_perm));
                assert(thread.is_free == false);
                assert(thread.parent != 0);
                
                assert(self.scheduler.pointer_list_len < NUM_THREAD);
                let index = self.scheduler.push(thread_ptr);
                thread.scheduler_node_index = index;
                thread.scheduled = true;


                // self.free_thread_count = self.free_thread_count + 1;
                let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
                proof {
                    lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
                    (self.thread_perms.borrow_mut())
                        .tracked_insert(thread_ptr as int, (new_thread_perm).get());
                } 
            }

        pub fn pop_schedule_thread(&mut self) -> (thread_ptr : ThreadPtr) 
            requires 
                old(self).wf_free_proc(),
                old(self).scheduler.len() > 0, 
                old(self).wf_free_thread(),
                old(self).wf_thread_ownership(),
                old(self).wf_scheduler(),
            ensures 
                self.wf_free_proc(),
                self.scheduler.len() ==  old(self).scheduler.len() - 1, // same, can be infered probably, but too hard
                self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == false,
                self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == false,
                self.wf_free_thread(),
                self.wf_thread_ownership(),
                self.wf_scheduler(),
                self.scheduler@ == old(self).scheduler@.subrange(1, old(self).scheduler.len() as int),
        {
            let thread_ptr = self.scheduler.pop();

            let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
            assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
            let tracked mut thread_perm: PointsTo<Thread> =
                (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int);
            assert(thread_perm@.pptr == thread_ptr as int);
            assert(thread_ptr as int == thread_pptr.id());
            let mut thread = thread_pptr.take(Tracked(&mut thread_perm));
            assert(thread.is_free == false);
            assert(thread.parent != 0);
            
            thread.scheduled = false;


            // self.free_thread_count = self.free_thread_count + 1;
            let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
            proof {
                lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
                (self.thread_perms.borrow_mut())
                    .tracked_insert(thread_ptr as int, (new_thread_perm).get());
            } 
            return thread_ptr;
        }

        pub fn remove_schedule_thread(&mut self, thread_ptr: ThreadPtr) 
            requires 
                old(self).wf_free_proc(),
                old(self).scheduler.len() > 0, 
                old(self).wf_free_thread(),
                old(self).wf_thread_ownership(),
                old(self).wf_scheduler(),
                old(self).scheduler@.contains(thread_ptr)
            ensures 
                self.wf_free_proc(),
                self.scheduler.len() ==  old(self).scheduler.len() - 1, // same, can be infered probably, but too hard
                self.thread_perms@[thread_ptr as int].view().value.get_Some_0().is_free == false,
                self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == false,
                self.wf_free_thread(),
                self.wf_thread_ownership(),
                self.wf_scheduler(),
                forall| pointer:ThreadPtr|  #![auto]  thread_ptr != pointer ==> old(self).scheduler@.contains(pointer) == self.scheduler@.contains(pointer),
                self.scheduler@.contains(thread_ptr) == false,
                // self.scheduler@ == old(self).scheduler@.subrange(1, old(self).scheduler.len() as int),
        {
            let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr as usize);
            assert(self.thread_perms@[thread_ptr as int].view().pptr == thread_ptr as int);
            let tracked mut thread_perm: PointsTo<Thread> =
                (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr as int);
            assert(thread_perm@.pptr == thread_ptr as int);
            assert(thread_ptr as int == thread_pptr.id());
            let mut thread = thread_pptr.take(Tracked(&mut thread_perm));
            assert(thread.is_free == false);
            assert(thread.scheduled == true);

            let index = thread.scheduler_node_index;
            thread.scheduled = false;
            // thread.parent_node_index = -1;
            
            let index_in_list:Ghost<int> = Ghost(self.scheduler@.index_of(thread_ptr));
            assert(0<= index_in_list@ < self.scheduler@.len());
            assert(self.scheduler@[index_in_list@] == thread_ptr);
            assert(self.scheduler.pointer_list@[index_in_list@] == index);
            assert(self.scheduler.arr_seq@[index as int].ptr == thread_ptr);

            let (new_thread_pptr, new_thread_perm) = PPtr::new(thread);
            proof {
                lemma_same_raw_ptr(new_thread_pptr.id(), thread_ptr as int);
                (self.thread_perms.borrow_mut())
                    .tracked_insert(thread_ptr as int, (new_thread_perm).get());
            } 
            // assert(self.thread_perms@[thread_ptr as int].view().value.get_Some_0().scheduled == false);
            self.scheduler.remove(index);

        }
    }
}