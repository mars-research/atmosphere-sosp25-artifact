use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;

    pub struct Process{
        pub owning_container: ContainerPtr,
        pub rev_ptr: SLLIndex,
        pub pcid: Pcid,
        pub ioid: Option<IOid>,
        pub owned_threads: StaticLinkedList<ThreadPtr, MAX_NUM_THREADS_PER_PROC>,

        pub parent: Option<ProcPtr>,
        pub parent_rev_ptr: Option<SLLIndex>,
        pub children: StaticLinkedList<ProcPtr,PROC_CHILD_LIST_LEN>,
        pub uppertree_seq: Ghost<Seq<ProcPtr>>,
        pub subtree_set: Ghost<Set<ProcPtr>>,
        pub depth: usize,

        pub dmd_paging_mode: DemandPagingMode,
    }
}