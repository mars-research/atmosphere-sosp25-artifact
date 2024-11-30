pub owned_procs: StaticLinkedList<ProcPtr,CONTAINER_PROC_LIST_LEN>,
pub parent: Option<ContainerPtr>,
pub parent_rev_ptr: Option<SLLIndex>,

pub children: StaticLinkedList<ContainerPtr,CONTAINER_CHILD_LIST_LEN>,

pub owned_endpoints: StaticLinkedList<EndpointPtr,CONTAINER_ENDPOINT_LIST_LEN>,

pub mem_quota: usize, 
// pub mem_quota_2m: usize,        
// pub mem_quota_1g: usize,

pub mem_used: usize,
// pub mem_used_2m: usize,
// pub mem_used_1g: usize,

pub owned_cpus: ArraySet<NUM_CPUS>,
pub scheduler: StaticLinkedList<ThreadPtr,MAX_CONTAINER_SCHEDULER_LEN>,

pub owned_threads: Ghost<Set<ThreadPtr>>,

pub depth:usize,

pub uppertree_seq: Ghost<Seq<ContainerPtr>>,
pub subtree_set: Ghost<Set<ContainerPtr>>,

    self.get_container(c_ptr).owned_procs =~= old(self).get_container(c_ptr).owned_procs,
    self.get_container(c_ptr).parent =~= old(self).get_container(c_ptr).parent,
    self.get_container(c_ptr).parent_rev_ptr =~= old(self).get_container(c_ptr).parent_rev_ptr,
    self.get_container(c_ptr).children =~= old(self).get_container(c_ptr).children,
    self.get_container(c_ptr)owned_endpoints. =~= old(self).get_container(c_ptr).owned_endpoints,
    self.get_container(c_ptr).mem_quota =~= old(self).get_container(c_ptr).mem_quota,
    self.get_container(c_ptr).mem_used =~= old(self).get_container(c_ptr).mem_used,
    self.get_container(c_ptr).owned_cpus =~= old(self).get_container(c_ptr).owned_cpus,
    self.get_container(c_ptr).scheduler =~= old(self).get_container(c_ptr).scheduler,
    self.get_container(c_ptr).owned_threads =~= old(self).get_container(c_ptr).owned_threads,
    self.get_container(c_ptr).depth =~= old(self).get_container(c_ptr).depth,
    self.get_container(c_ptr).uppertree_seq =~= old(self).get_container(c_ptr).uppertree_seq,
    self.get_container(c_ptr).subtree_set =~= old(self).get_container(c_ptr).subtree_set,
    self.get_container(c_ptr). =~= old(self).get_container(c_ptr).,