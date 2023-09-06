

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

    #[verifier(external_body)]
    pub fn page_to_proc(page: (PPtr::<PageMem>,Tracked<PointsTo<PageMem>>)) -> (ret :(PPtr::<Process>, Tracked<PointsTo<Process>>))
        requires page.0.id() == page.1@@.pptr,
                 page.1@@.value.is_Some(),
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == page.0.id(),
                ret.1@@.value.is_Some(),
                ret.1@@.value.get_Some_0().owned_threads.wf(),
                ret.1@@.value.get_Some_0().owned_threads.len() == 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub fn page_to_thread(page: (PPtr::<PageMem>,Tracked<PointsTo<PageMem>>)) -> (ret :(PPtr::<Thread>, Tracked<PointsTo<Thread>>))
        requires page.0.id() == page.1@@.pptr,
                 page.1@@.value.is_Some(),
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == page.0.id(),
                ret.1@@.value.is_Some(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub fn proc_to_page(proc: (PPtr::<Process>, Tracked<PointsTo<Process>>)) -> (ret : (PPtr::<PageMem>,Tracked<PointsTo<PageMem>>))
        requires proc.0.id() == proc.1@@.pptr,
                 proc.1@@.value.is_Some(),
                 proc.1@@.value.get_Some_0().owned_threads.len() == 0,
        ensures ret.0.id() == ret.1@@.pptr,
                ret.0.id() == proc.0.id(),
                ret.1@@.value.is_Some(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    proof fn lemma_unique_ptr<T>(ptr:usize, map: &Tracked<Map<usize, T>>)
        ensures
            map@.dom().contains(ptr) == false,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub fn proc_set_needle(pptr: &PPtr::<Process>,perm: &mut Tracked<PointsTo<Process>>, needle: Needle)
        requires pptr.id() == old(perm)@@.pptr,
                 old(perm)@@.value.is_Some(),
        ensures pptr.id() == perm@@.pptr,
                perm@@.value.is_Some(),
                perm@@.value.get_Some_0().owned_threads == old(perm)@@.value.get_Some_0().owned_threads,
                perm@@.value.get_Some_0().needle == needle,
    {
        unsafe {
            let uptr = pptr.to_usize() as *mut MaybeUninit<Process>;
            (*uptr).assume_init_mut().needle = needle;
        }
    }

    #[verifier(external_body)]
    pub fn thread_set_needle(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, needle: Needle)
        requires pptr.id() == old(perm)@@.pptr,
                 old(perm)@@.value.is_Some(),
        ensures pptr.id() == perm@@.pptr,
                perm@@.value.is_Some(),
                perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
                perm@@.value.get_Some_0().parent_needle == old(perm)@@.value.get_Some_0().parent_needle,
                perm@@.value.get_Some_0().scheduled == old(perm)@@.value.get_Some_0().scheduled,
                perm@@.value.get_Some_0().scheduler_needle == old(perm)@@.value.get_Some_0().scheduler_needle,
                perm@@.value.get_Some_0().needle == needle,
    {
        unsafe {
            let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
            (*uptr).assume_init_mut().needle = needle;
        }
    }

    #[verifier(external_body)]
    pub fn thread_set_parent_needle(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent_needle: Needle)
        requires pptr.id() == old(perm)@@.pptr,
                 old(perm)@@.value.is_Some(),
        ensures pptr.id() == perm@@.pptr,
                perm@@.value.is_Some(),
                perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
                perm@@.value.get_Some_0().needle == old(perm)@@.value.get_Some_0().needle,
                perm@@.value.get_Some_0().scheduled == old(perm)@@.value.get_Some_0().scheduled,
                perm@@.value.get_Some_0().scheduler_needle == old(perm)@@.value.get_Some_0().scheduler_needle,
                perm@@.value.get_Some_0().parent_needle == parent_needle,
    {
        unsafe {
            let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
            (*uptr).assume_init_mut().parent_needle = parent_needle;
        }
    }

    #[verifier(external_body)]
    pub fn thread_set_parent(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent: ProcPtr)
        requires pptr.id() == old(perm)@@.pptr,
                 old(perm)@@.value.is_Some(),
        ensures pptr.id() == perm@@.pptr,
                perm@@.value.is_Some(),
                perm@@.value.get_Some_0().parent_needle == old(perm)@@.value.get_Some_0().parent_needle,
                perm@@.value.get_Some_0().needle == old(perm)@@.value.get_Some_0().needle,
                perm@@.value.get_Some_0().scheduled == old(perm)@@.value.get_Some_0().scheduled,
                perm@@.value.get_Some_0().scheduler_needle == old(perm)@@.value.get_Some_0().scheduler_needle,
                perm@@.value.get_Some_0().parent == parent,
    {
        unsafe {
            let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
            (*uptr).assume_init_mut().parent = parent;
        }
    }

    // #[verifier(external_body)]
    // pub fn proc_push_thread(pptr: &PPtr::<Process>,perm: &mut Tracked<PointsTo<Process>>) -> (ret : Needle)
    //     requires pptr.id() == old(perm)@@.pptr,
    //              old(perm)@@.value.is_Some(),
    //     ensures pptr.id() == perm@@.pptr,
    //             perm@@.value.is_Some(),
    //             perm@@.value.get_Some_0().owned_threads == old(perm)@@.value.get_Some_0().owned_threads,
    //             perm@@.value.get_Some_0().needle == ret,
    // {
    //     unsafe {
    //         let uptr = pptr.to_usize() as *mut MaybeUninit<Process>;
    //         let ret:Needle = (*uptr).assume_init_mut().owned_threads.push(pptr.to_usize());
    //         return ret;
    //     }
    // }


    pub struct Process{
        pub needle : Needle,
        pub owned_threads: MarsLinkedList,
    }

    pub struct Thread{
        pub needle : Needle,
        pub parent: ProcPtr,
        pub parent_needle: Needle,
        pub scheduled: bool,
        pub scheduler_needle: Needle,
    }
    
    pub struct ProcessManager{
        pub proc_ptrs: MarsLinkedList,
        pub proc_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
        pub thread_ptrs: MarsLinkedList,
        pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
        
        pub scheduler: MarsLinkedList,
    }

    impl ProcessManager {
        pub open spec fn wf_procs(&self) -> bool{
            (
            self.proc_ptrs.wf()
            )
            &&            
            (self.proc_ptrs.is_unique()
            )
            &&
            (
            self.proc_ptrs@.to_set() =~= self.proc_perms@.dom()
            )
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.is_Some())
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().pptr == i)
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.get_Some_0().owned_threads.wf())
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.get_Some_0().owned_threads.is_unique())
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_valid(&self.proc_perms@[i].view().value.get_Some_0().needle))
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_resolve(&self.proc_perms@[i].view().value.get_Some_0().needle) == i)
        }

        pub open spec fn wf_threads(&self) -> bool{
            (
            self.thread_ptrs.wf()
            )
            &&   
            (
                self.thread_ptrs.is_unique()
                )
                &&
            (
            self.thread_ptrs@.to_set() =~= self.thread_perms@.dom()
            )
            &&
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.thread_perms@[i].view().value.is_Some())
            &&
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.thread_perms@[i].view().pptr == i)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_ptrs@.contains(self.thread_perms@[i].view().value.get_Some_0().parent))
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(i))
            && 
            (forall|proc_ptr: usize, thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
                ==>  self.thread_perms@.dom().contains(thread_ptr))
            && 
            (forall|proc_ptr: usize, thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(proc_ptr) && self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr)
                    ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().parent == proc_ptr)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
              self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().parent_needle)  == true)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
                self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().parent_needle) == i)            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
                self.thread_ptrs.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().needle) == true)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
                self.thread_ptrs.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().needle) == i)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) && self.thread_perms@[i].view().value.get_Some_0().scheduled == true ==>
                self.scheduler.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().scheduler_needle) == true)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) && self.thread_perms@[i].view().value.get_Some_0().scheduled == true ==>
                self.scheduler.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().scheduler_needle) == i)
        }

        pub open spec fn wf(&self) -> bool{
            self.wf_threads()
            &&
            self.wf_procs()
        }

        pub fn new_proc(&mut self, page : (PPtr::<PageMem>, Tracked<PointsTo<PageMem>>))
            requires old(self).wf(),
                     old(self).proc_ptrs.len() < old(self).proc_ptrs.capacity(),
                     page.0.id() == page.1@@.pptr,
                     page.1@@.value.is_Some(),
                     old(self).proc_ptrs@.contains(page.0.id() as ProcPtr) == false,
            ensures 
                    self.wf(),
                    self.proc_ptrs.len() == old(self).proc_ptrs.len() + 1,
        {
            let (pptr,mut perm) = page_to_proc(page);
            let ptr = pptr.to_usize();
            let needle = self.proc_ptrs.push(ptr);
            proc_set_needle(&pptr, &mut perm, needle);
            proof {
                assert(self.proc_perms@.dom().contains(ptr) == false);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(ptr, (perm).get());
            } 
            assert((forall|i: usize| #![auto] old(self).proc_perms@.dom().contains(i) ==>  self.proc_perms@[i] == old(self).proc_perms@[i]));
            assert(self.thread_ptrs.wf());
            // assert(forall|i: int| #![auto] 0 <= i < self.thread_ptrs.len() ==> self.thread_perms@.dom().contains(self.thread_ptrs@[i]));
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.thread_perms@[i].view().value.is_Some());
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.thread_perms@[i].view().pptr == i);
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_ptrs@.contains(self.thread_perms@[i].view().value.get_Some_0().parent));
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(i));
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(i));
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
            //     self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().parent_needle)  == true);
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
            //     self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().parent_needle) == i);
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) && self.thread_perms@[i].view().value.get_Some_0().scheduled == true ==>
            //     self.scheduler.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().scheduler_needle) == true);
            // assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) && self.thread_perms@[i].view().value.get_Some_0().scheduled == true ==>
            //     self.scheduler.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().scheduler_needle) == i);
            assert(self.wf_threads());
            assert(self.proc_ptrs.wf());
            // assert(old(self).proc_ptrs.is_unique());
            // assert(self.proc_ptrs@.to_set() =~= self.proc_perms@.dom());
            // assert(forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.is_Some());
            // assert(forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().pptr == i);
            // assert(forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.get_Some_0().owned_threads.wf());
            // assert(forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_valid(&self.proc_perms@[i].view().value.get_Some_0().needle));
            // assert(forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_ptrs.needle_resolve(&self.proc_perms@[i].view().value.get_Some_0().needle) == i);

            assert(self.wf_procs());
        }

        pub fn free_proc(&mut self, proc_ptr:ProcPtr) -> (ret : (PPtr::<PageMem>, Tracked<PointsTo<PageMem>>))
            requires old(self).wf(),
                     old(self).proc_ptrs.len() > 0,
                     old(self).proc_ptrs@.contains(proc_ptr),
                     old(self).proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.len() == 0,
            ensures self.wf(),
                    self.proc_ptrs.len() == old(self).proc_ptrs.len() - 1,
                    ret.0.id() == ret.1@@.pptr,
                    ret.0.id() == proc_ptr,
                    ret.1@@.value.is_Some(),
        {
            assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(i));
            assert(self.proc_perms@.dom().contains(proc_ptr));
            assert(self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.wf());
            assert(self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads@.len() == 0);
            assert(forall|i: usize| #![auto] self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads@.contains(i) == false);
            assert(forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==> self.thread_perms@[i].view().value.get_Some_0().parent != proc_ptr);

            assert(self.proc_ptrs.needle_resolve(&self.proc_perms@[proc_ptr].view().value.get_Some_0().needle) == proc_ptr);

            let tracked proc_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr);

            let pptr: PPtr<Process> = PPtr::<Process>::from_usize(proc_ptr);
            assert(proc_perm@.pptr == pptr.id());
            assert(proc_perm@.value.is_Some());
            let proc : &Process = pptr.borrow(Tracked(&proc_perm));
            self.proc_ptrs.remove(&proc.needle);
            assert(self.proc_ptrs@.contains(proc_ptr) == false);
            
            let ret = proc_to_page((pptr, Tracked(proc_perm)));
            assert(self.wf_threads());
            assert(self.wf_procs());
            return ret;
        }

        pub fn new_thread_for_proc(&mut self, proc_ptr:ProcPtr, page : (PPtr::<PageMem>, Tracked<PointsTo<PageMem>>)) -> (ret: ThreadPtr)
            requires old(self).wf(),
                     page.0.id() == page.1@@.pptr,
                     page.1@@.value.is_Some(),
                     old(self).proc_ptrs.len() > 0,
                     old(self).thread_ptrs.len() < old(self).thread_ptrs.capacity(),
                     old(self).proc_ptrs@.contains(proc_ptr),
                     old(self).proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.len() < old(self).proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.capacity(),
                     old(self).thread_ptrs@.contains(page.0.id() as ProcPtr) == false,
            ensures self.wf(),
        {

            let (thread_pptr,mut thread_perm) = page_to_thread(page);

            let thread_ptr = thread_pptr.to_usize();

            assert(forall|_proc_ptr: usize, _thread_ptr: usize| #![auto] self.proc_perms@.dom().contains(_proc_ptr) && self.proc_perms@[_proc_ptr]@.value.get_Some_0().owned_threads@.contains(_thread_ptr)
                ==>  self.thread_perms@.dom().contains(_thread_ptr));
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            assert(self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@.contains(thread_ptr) == false);

            assert(self.proc_perms@.dom().contains(proc_ptr));
            let tracked mut proc_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr);
            let proc_pptr: PPtr<Process> = PPtr::<Process>::from_usize(proc_ptr);
            assert(proc_ptr == proc_perm@.pptr);
            let mut proc_copy = proc_pptr.take(Tracked(&mut proc_perm));
            let parent_needle = proc_copy.owned_threads.push(thread_pptr.to_usize());
            let proc_copy = proc_pptr.put(Tracked(&mut proc_perm), proc_copy);

            
            proof {
                assert(self.proc_perms@.dom().contains(proc_ptr) == false);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(proc_ptr, proc_perm);
            } 
            assert(self.wf_procs());

            let thread_ptr = thread_pptr.to_usize();
            let needle = self.thread_ptrs.push(thread_ptr);
            thread_set_needle(&thread_pptr, &mut thread_perm, needle);
            thread_set_parent_needle(&thread_pptr, &mut thread_perm, parent_needle);
            thread_set_parent(&thread_pptr, &mut thread_perm, proc_ptr);

            proof {
                assert(self.thread_perms@.dom().contains(thread_ptr) == false);
                (self.thread_perms.borrow_mut())
                    .tracked_insert(thread_ptr, (thread_perm).get());
            } 
            assert(self.wf_threads());
            0
        }
        pub fn free_thread_for_proc(&mut self, proc_ptr:ProcPtr, thread_ptr:ThreadPtr) 
        //-> (ret : (PPtr::<PageMem>, Tracked<PointsTo<PageMem>>))
            requires old(self).wf(),
                     old(self).proc_ptrs.len() > 0,
                     old(self).thread_ptrs.len() > 0,
                     old(self).proc_ptrs@.contains(proc_ptr),
                     old(self).proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads@.contains(thread_ptr),
            ensures self.wf(),
        {
            assert(self.thread_ptrs@.contains(thread_ptr));
            assert(self.thread_perms@[thread_ptr]@.value.get_Some_0().parent == proc_ptr);

            let tracked mut thread_perm: PointsTo<Thread> =
                (self.thread_perms.borrow_mut()).tracked_remove(thread_ptr);
            assert(thread_ptr == thread_perm@.pptr);
            let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(&thread_perm));

            assert(self.proc_perms@.dom().contains(proc_ptr));
            let tracked mut proc_perm: PointsTo<Process> =
                (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr);
            let proc_pptr: PPtr<Process> = PPtr::<Process>::from_usize(proc_ptr);
            assert(proc_ptr == proc_perm@.pptr);
            let mut proc_copy = proc_pptr.take(Tracked(&mut proc_perm));
            proc_copy.owned_threads.remove(&thread.parent_needle);
            assert(proc_copy.owned_threads@.contains(thread_ptr) == false);
            let proc_copy = proc_pptr.put(Tracked(&mut proc_perm), proc_copy);

            proof {
                assert(self.proc_perms@.dom().contains(proc_ptr) == false);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(proc_ptr, proc_perm);
            } 
            assert(self.wf_procs());

            self.thread_ptrs.remove(&thread.needle);
            assert(self.thread_ptrs@.contains(thread_ptr) == false);
            assert(self.wf_threads());
        }
    }
}