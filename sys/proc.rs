

use super::*;

pub const NUM_PROCESS: usize = 2;
pub const THREAD_PRE_PROC: usize = 2;
pub const NUM_THREAD: usize = NUM_PROCESS * 4;
pub type ProcID = usize;
pub type ThreadID = usize;
pub type ProcPtr = usize;
pub type ThreadPtr = usize;

use core::mem::MaybeUninit;


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
        pub proc_perms: Tracked<Map<usize, PointsTo<Process>>>,
        pub thread_ptrs: MarsLinkedList,
        pub thread_perms: Tracked<Map<usize, PointsTo<Thread>>>,
        
        pub scheduler: MarsLinkedList,
    }

    impl ProcessManager {
        pub open spec fn wf_procs(&self) -> bool{
            (
            self.proc_ptrs.wf()
            )
            &&
            (
            forall|i: int| #![auto] 0 <= i < self.proc_ptrs.len() ==> self.proc_perms@.dom().contains(self.proc_ptrs@[i])
            )
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.is_Some())
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().pptr == i)
            &&
            (forall|i: usize| #![auto] self.proc_perms@.dom().contains(i) ==>  self.proc_perms@[i].view().value.get_Some_0().owned_threads.wf())
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
            forall|i: int| #![auto] 0 <= i < self.thread_ptrs.len() ==> self.thread_perms@.dom().contains(self.thread_ptrs@[i])
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
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>  self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads@.contains(i))
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
              self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_valid(&self.thread_perms@[i].view().value.get_Some_0().parent_needle)  == true)
            && 
            (forall|i: usize| #![auto] self.thread_perms@.dom().contains(i) ==>
                self.proc_perms@[self.thread_perms@[i].view().value.get_Some_0().parent].view().value.get_Some_0().owned_threads.needle_resolve(&self.thread_perms@[i].view().value.get_Some_0().parent_needle) == i)
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

        {
            let (pptr,mut perm) = page_to_proc(page);
            let ptr = pptr.to_usize();
            let needle = self.proc_ptrs.push(ptr);
            proc_set_needle(&pptr, &mut perm, needle);
            proof {
                lemma_unique_ptr(ptr, &self.proc_perms);
                (self.proc_perms.borrow_mut())
                    .tracked_insert(ptr, (perm).get());
            } 
            assert((forall|i: usize| #![auto] old(self).proc_perms@.dom().contains(i) ==>  self.proc_perms@[i] == old(self).proc_perms@[i]));
            assert(self.wf_threads());
        }

    }
}