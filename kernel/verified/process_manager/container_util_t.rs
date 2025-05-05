use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::container::*;
use crate::array_set::ArraySet;
use crate::quota::Quota;

#[verifier(external_body)]
pub fn scheduler_push_thread(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, thread_ptr: &ThreadPtr) -> (ret: SLLIndex)
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        old(container_perm)@.value().scheduler@.contains(*thread_ptr) == false,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        // container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,


        container_perm@.value().scheduler.wf(),
        container_perm@.value().scheduler@ == old(container_perm)@.value().scheduler@.push(*thread_ptr),
        container_perm@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_valid(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> container_perm@.value().scheduler.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().scheduler.node_ref_resolve(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> container_perm@.value().scheduler.node_ref_resolve(index) == old(container_perm)@.value().scheduler.node_ref_resolve(index),
        container_perm@.value().scheduler.node_ref_valid(ret),
        container_perm@.value().scheduler.node_ref_resolve(ret) == *thread_ptr,
        container_perm@.value().scheduler.unique(),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().scheduler.push(thread_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn scheduler_pop_head(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>) -> (ret:(ThreadPtr,SLLIndex))
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler.len() != 0,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,


        container_perm@.value().scheduler.wf(),
        container_perm@.value().scheduler.unique(),
        container_perm@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() - 1,
        container_perm@.value().scheduler@ == old(container_perm)@.value().scheduler@.skip(1),
        ret.0 == old(container_perm)@.value().scheduler@[0],
        old(container_perm)@.value().scheduler.value_list@[0] == ret.1,
        old(container_perm)@.value().scheduler.node_ref_valid(ret.1),
        old(container_perm)@.value().scheduler.node_ref_resolve(ret.1) == ret.0,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_valid(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) && index != ret.1 ==> container_perm@.value().scheduler.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().scheduler.node_ref_resolve(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) && index != ret.1 ==> container_perm@.value().scheduler.node_ref_resolve(index) == old(container_perm)@.value().scheduler.node_ref_resolve(index),
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_valid(index)]
            #![trigger old(container_perm)@.value().scheduler.node_ref_resolve(index)]
            #![trigger container_perm@.value().scheduler.node_ref_resolve(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) && old(container_perm)@.value().scheduler.node_ref_resolve(index) != ret.0 
            ==> 
            container_perm@.value().scheduler.node_ref_valid(index)
            &&
            container_perm@.value().scheduler.node_ref_resolve(index) == old(container_perm)@.value().scheduler.node_ref_resolve(index),
    {
        unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().scheduler.pop();
        ret
        }
    }

#[verifier(external_body)]
pub fn container_push_proc(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, p_ptr: ProcPtr) -> (ret: SLLIndex)
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_procs.wf(),
        old(container_perm)@.value().owned_procs.unique(),
        old(container_perm)@.value().owned_procs.len() < CONTAINER_PROC_LIST_LEN,
        old(container_perm)@.value().owned_procs@.contains(p_ptr) == false,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        // container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().owned_procs.wf(),
        container_perm@.value().owned_procs@ == old(container_perm)@.value().owned_procs@.push(p_ptr),
        container_perm@.value().owned_procs.len() == old(container_perm)@.value().owned_procs.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().owned_procs.node_ref_valid(index)]
            #![trigger container_perm@.value().owned_procs.node_ref_valid(index)]
            old(container_perm)@.value().owned_procs.node_ref_valid(index) ==> container_perm@.value().owned_procs.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().owned_procs.node_ref_valid(index)]
            old(container_perm)@.value().owned_procs.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().owned_procs.node_ref_valid(index)]
            #![trigger container_perm@.value().owned_procs.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().owned_procs.node_ref_resolve(index)]
            old(container_perm)@.value().owned_procs.node_ref_valid(index) ==> container_perm@.value().owned_procs.node_ref_resolve(index) == old(container_perm)@.value().owned_procs.node_ref_resolve(index),
        container_perm@.value().owned_procs.node_ref_valid(ret),
        container_perm@.value().owned_procs.node_ref_resolve(ret) == p_ptr,
        container_perm@.value().owned_procs.unique(),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().owned_procs.push(&p_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn container_push_child(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, c_ptr: ContainerPtr) -> (ret: SLLIndex)
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().children.wf(),
        old(container_perm)@.value().children.unique(),
        old(container_perm)@.value().children.len() < CONTAINER_CHILD_LIST_LEN,
        old(container_perm)@.value().children@.contains(c_ptr) == false,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        // container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().children.wf(),
        container_perm@.value().children@ == old(container_perm)@.value().children@.push(c_ptr),
        container_perm@.value().children.len() == old(container_perm)@.value().children.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().children.node_ref_valid(index)]
            #![trigger container_perm@.value().children.node_ref_valid(index)]
            old(container_perm)@.value().children.node_ref_valid(index) ==> container_perm@.value().children.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().children.node_ref_valid(index)]
            old(container_perm)@.value().children.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().children.node_ref_valid(index)]
            #![trigger container_perm@.value().children.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().children.node_ref_resolve(index)]
            old(container_perm)@.value().children.node_ref_valid(index) ==> container_perm@.value().children.node_ref_resolve(index) == old(container_perm)@.value().children.node_ref_resolve(index),
        container_perm@.value().children.node_ref_valid(ret),
        container_perm@.value().children.node_ref_resolve(ret) == c_ptr,
        container_perm@.value().children.unique(),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().children.push(&c_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn container_push_endpoint(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, e_ptr: EndpointPtr) -> (ret: SLLIndex)
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_endpoints.wf(),
        old(container_perm)@.value().owned_endpoints.unique(),
        old(container_perm)@.value().owned_endpoints.len() < CONTAINER_ENDPOINT_LIST_LEN,
        old(container_perm)@.value().owned_endpoints@.contains(e_ptr) == false,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        // container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().owned_endpoints.wf(),
        container_perm@.value().owned_endpoints@ == old(container_perm)@.value().owned_endpoints@.push(e_ptr),
        container_perm@.value().owned_endpoints.len() == old(container_perm)@.value().owned_endpoints.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().owned_endpoints.node_ref_valid(index)]
            #![trigger container_perm@.value().owned_endpoints.node_ref_valid(index)]
            old(container_perm)@.value().owned_endpoints.node_ref_valid(index) ==> container_perm@.value().owned_endpoints.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().owned_endpoints.node_ref_valid(index)]
            old(container_perm)@.value().owned_endpoints.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().owned_endpoints.node_ref_valid(index)]
            #![trigger container_perm@.value().owned_endpoints.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().owned_endpoints.node_ref_resolve(index)]
            old(container_perm)@.value().owned_endpoints.node_ref_valid(index) ==> container_perm@.value().owned_endpoints.node_ref_resolve(index) == old(container_perm)@.value().owned_endpoints.node_ref_resolve(index),
        container_perm@.value().owned_endpoints.node_ref_valid(ret),
        container_perm@.value().owned_endpoints.node_ref_resolve(ret) == e_ptr,
        container_perm@.value().owned_endpoints.unique(),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().owned_endpoints.push(&e_ptr);
        return ret;
    }
}


#[verifier(external_body)]
pub fn container_set_quota_mem_4k(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, value: usize) 
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().quota =~= old(container_perm)@.value().quota.spec_set_mem_4k(value),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().quota.set_mem_4k(value);
    }
}

#[verifier(external_body)]
pub fn container_set_quota(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, new_quota: &Quota) 
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().quota =~= *new_quota,
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().quota = *new_quota;
    }
}

#[verifier(external_body)]
pub fn container_set_owned_threads(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, owned_threads: Ghost<Set<ThreadPtr>>) 
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        // container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(container_perm)@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,

        container_perm@.value().owned_threads =~= owned_threads,
{
}

#[verifier(external_body)]
pub fn page_to_container(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, first_proc:ProcPtr, parent_container:ContainerPtr, 
    parent_rev_ptr:SLLIndex, init_quota:Quota, new_cpus: ArraySet<NUM_CPUS>, first_thread:ThreadPtr) -> (ret:(SLLIndex,SLLIndex,ContainerPtr,Tracked<PointsTo<Container>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.3@.is_init(),
        ret.2 == page_ptr,
        ret.3@.addr() == page_ptr, 
        ret.3@.value().owned_procs.wf(),        
        ret.3@.value().owned_procs@ =~= Seq::<ProcPtr>::empty().push(first_proc),
        ret.3@.value().owned_procs.len() == 1,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().owned_procs.node_ref_valid(index)] 
            index != ret.0
            ==>
            ret.3@.value().owned_procs.node_ref_valid(index) == false,
        ret.3@.value().owned_procs.node_ref_valid(ret.0),
        ret.3@.value().owned_procs.node_ref_resolve(ret.0) == first_proc,
        ret.3@.value().parent =~= Some(parent_container),
        ret.3@.value().parent_rev_ptr =~= Some(parent_rev_ptr),
        ret.3@.value().children.wf(),        
        ret.3@.value().children@ =~= Seq::<ContainerPtr>::empty(),
        ret.3@.value().children.len() == 0,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().children.node_ref_valid(index)] 
            ret.3@.value().children.node_ref_valid(index) == false,
        ret.3@.value().owned_endpoints.wf(),        
        ret.3@.value().owned_endpoints@ =~= Seq::<EndpointPtr>::empty(),
        ret.3@.value().owned_endpoints.len() == 0,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().owned_endpoints.node_ref_valid(index)] 
            ret.3@.value().owned_endpoints.node_ref_valid(index) == false,
        ret.3@.value().quota =~= init_quota,
        // ret.3@.value().mem_used =~= 0,
        ret.3@.value().owned_cpus =~= new_cpus,

        ret.3@.value().scheduler.wf(),        
        ret.3@.value().scheduler@ =~= Seq::<ThreadPtr>::empty().push(first_thread),
        ret.3@.value().scheduler.len() == 1,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().scheduler.node_ref_valid(index)] 
            index != ret.1
            ==>
            ret.3@.value().scheduler.node_ref_valid(index) == false,
        ret.3@.value().scheduler.node_ref_valid(ret.1),
        ret.3@.value().scheduler.node_ref_resolve(ret.1) == first_thread,
        ret.3@.value().owned_threads@ =~= Set::<ThreadPtr>::empty().insert(first_thread),
        ret.3@.value().can_have_children =~= false,
        ret.3@.value().root_process =~= Some(first_proc),
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().owned_procs.init();
        let sll1 = (*uptr).assume_init_mut().owned_procs.push(&first_proc);
        (*uptr).assume_init_mut().parent = Some(parent_container);
        (*uptr).assume_init_mut().parent_rev_ptr = Some(parent_rev_ptr);
        (*uptr).assume_init_mut().children.init();
        (*uptr).assume_init_mut().owned_endpoints.init();
        (*uptr).assume_init_mut().quota = init_quota;
        // (*uptr).assume_init_mut().mem_used = 0;
        (*uptr).assume_init_mut().owned_cpus = new_cpus;
        (*uptr).assume_init_mut().scheduler.init();
        let sll2 = (*uptr).assume_init_mut().scheduler.push(&first_thread);
        (*uptr).assume_init_mut().root_process = Some(first_proc);
        (sll1,sll2,page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn page_to_container_tree_version(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, first_proc:ProcPtr, parent_container:ContainerPtr, parent_rev_ptr:SLLIndex, 
        init_quota:Quota, new_cpus: ArraySet<NUM_CPUS>, first_thread:ThreadPtr, depth:usize, subtree_set: Ghost<Set<ContainerPtr>>, uppertree_seq: Ghost<Seq<ContainerPtr>>) 
            -> (ret:(SLLIndex,SLLIndex,ContainerPtr,Tracked<PointsTo<Container>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.3@.is_init(),
        ret.2 == page_ptr,
        ret.3@.addr() == page_ptr, 
        ret.3@.value().owned_procs.wf(),        
        ret.3@.value().owned_procs@ =~= Seq::<ProcPtr>::empty().push(first_proc),
        ret.3@.value().owned_procs.len() == 1,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().owned_procs.node_ref_valid(index)] 
            index != ret.0
            ==>
            ret.3@.value().owned_procs.node_ref_valid(index) == false,
        ret.3@.value().owned_procs.node_ref_valid(ret.0),
        ret.3@.value().owned_procs.node_ref_resolve(ret.0) == first_proc,
        ret.3@.value().parent =~= Some(parent_container),
        ret.3@.value().parent_rev_ptr =~= Some(parent_rev_ptr),
        ret.3@.value().children.wf(),        
        ret.3@.value().children@ =~= Seq::<ContainerPtr>::empty(),
        ret.3@.value().children.len() == 0,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().children.node_ref_valid(index)] 
            ret.3@.value().children.node_ref_valid(index) == false,
        ret.3@.value().owned_endpoints.wf(),        
        ret.3@.value().owned_endpoints@ =~= Seq::<EndpointPtr>::empty(),
        ret.3@.value().owned_endpoints.len() == 0,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().owned_endpoints.node_ref_valid(index)] 
            ret.3@.value().owned_endpoints.node_ref_valid(index) == false,
        ret.3@.value().quota =~= init_quota,
        // ret.3@.value().mem_used =~= 0,
        ret.3@.value().owned_cpus =~= new_cpus,

        ret.3@.value().scheduler.wf(),        
        ret.3@.value().scheduler@ =~= Seq::<ThreadPtr>::empty().push(first_thread),
        ret.3@.value().scheduler.len() == 1,
        forall|index:SLLIndex|
            #![trigger ret.3@.value().scheduler.node_ref_valid(index)] 
            index != ret.1
            ==>
            ret.3@.value().scheduler.node_ref_valid(index) == false,
        ret.3@.value().scheduler.node_ref_valid(ret.1),
        ret.3@.value().scheduler.node_ref_resolve(ret.1) == first_thread,
        ret.3@.value().owned_threads@ =~= Set::<ThreadPtr>::empty().insert(first_thread),

        ret.3@.value().depth =~= depth,
        ret.3@.value().subtree_set =~= subtree_set,
        ret.3@.value().uppertree_seq =~= uppertree_seq,

        ret.3@.value().can_have_children =~= false,
        ret.3@.value().root_process =~= Some(first_proc),
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().owned_procs.init();
        let sll1 = (*uptr).assume_init_mut().owned_procs.push(&first_proc);
        (*uptr).assume_init_mut().parent = Some(parent_container);
        (*uptr).assume_init_mut().parent_rev_ptr = Some(parent_rev_ptr);
        (*uptr).assume_init_mut().children.init();
        (*uptr).assume_init_mut().owned_endpoints.init();
        (*uptr).assume_init_mut().quota = init_quota;
        // (*uptr).assume_init_mut().mem_used = 0;
        (*uptr).assume_init_mut().owned_cpus = new_cpus;
        (*uptr).assume_init_mut().scheduler.init();
        (*uptr).assume_init_mut().depth = depth;
        let sll2 = (*uptr).assume_init_mut().scheduler.push(&first_thread);
        (*uptr).assume_init_mut().root_process = Some(first_proc);
        (sll1,sll2,page_ptr, Tracked::assume_new())
    }
}


#[verifier(external_body)]
pub fn page_to_container_tree_version_1(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, parent_container:ContainerPtr, parent_rev_ptr:SLLIndex, 
        init_quota:Quota, new_cpus: ArraySet<NUM_CPUS>,depth:usize, subtree_set: Ghost<Set<ContainerPtr>>, uppertree_seq: Ghost<Seq<ContainerPtr>>,
        root_process:Option<ProcPtr>) 
            -> (ret:(ContainerPtr,Tracked<PointsTo<Container>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.1@.is_init(),
        ret.0 == page_ptr,
        ret.1@.addr() == page_ptr, 
        ret.1@.value().owned_procs.wf(),        
        ret.1@.value().owned_procs@ =~= Seq::<ProcPtr>::empty(),
        // forall|index:SLLIndex|
        //     #![trigger ret.1@.value().owned_procs.node_ref_valid(index)] 
        //     ret.1@.value().owned_procs.node_ref_valid(index) == false,
        ret.1@.value().parent =~= Some(parent_container),
        ret.1@.value().parent_rev_ptr =~= Some(parent_rev_ptr),
        ret.1@.value().children.wf(),        
        ret.1@.value().children@ =~= Seq::<ContainerPtr>::empty(),
        ret.1@.value().children.len() == 0,
        // forall|index:SLLIndex|
        //     #![trigger ret.1@.value().children.node_ref_valid(index)] 
        //     ret.1@.value().children.node_ref_valid(index) == false,
        ret.1@.value().owned_endpoints.wf(),        
        ret.1@.value().owned_endpoints@ =~= Seq::<EndpointPtr>::empty(),
        ret.1@.value().owned_endpoints.len() == 0,
        ret.1@.value().quota =~= init_quota,
        // ret.1@.value().mem_used =~= 0,
        ret.1@.value().owned_cpus =~= new_cpus,

        ret.1@.value().scheduler.wf(),        
        ret.1@.value().scheduler@ =~= Seq::<ThreadPtr>::empty(),
        ret.1@.value().owned_threads@ =~= Set::<ThreadPtr>::empty(),

        ret.1@.value().depth =~= depth,
        ret.1@.value().subtree_set =~= subtree_set,
        ret.1@.value().uppertree_seq =~= uppertree_seq,

        ret.1@.value().root_process == root_process,

        ret.1@.value().can_have_children =~= false,
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().owned_procs.init();
        (*uptr).assume_init_mut().parent = Some(parent_container);
        (*uptr).assume_init_mut().parent_rev_ptr = Some(parent_rev_ptr);
        (*uptr).assume_init_mut().children.init();
        (*uptr).assume_init_mut().owned_endpoints.init();
        (*uptr).assume_init_mut().quota = init_quota;
        // (*uptr).assume_init_mut().mem_used = 0;
        (*uptr).assume_init_mut().owned_cpus = new_cpus;
        (*uptr).assume_init_mut().scheduler.init();
        (*uptr).assume_init_mut().depth = depth;
        (*uptr).assume_init_mut().root_process == root_process;
        (page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn container_perms_update_subtree_set(perms: &mut Tracked<Map<ContainerPtr, PointsTo<Container>>>, uppertree_seq: Ghost<Seq<ContainerPtr>>, new_container_ptr:ContainerPtr)
    ensures
        old(perms)@.dom() =~= perms@.dom(),
        forall|c_ptr:ContainerPtr| 
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger perms@.dom().contains(c_ptr)]
            #![trigger perms@[c_ptr]]
            perms@.dom().contains(c_ptr) && uppertree_seq@.contains(c_ptr) == false
            ==>               
            perms@[c_ptr] =~= old(perms)@[c_ptr],
        forall|c_ptr:ContainerPtr| 
            // #![trigger perms@[c_ptr].value().owning_container]
            #![trigger perms@.dom().contains(c_ptr)]
            #![trigger perms@[c_ptr]]
            perms@.dom().contains(c_ptr)
            ==>               
            perms@[c_ptr].is_init() =~= old(perms)@[c_ptr].is_init()
            &&
            perms@[c_ptr].addr() =~= old(perms)@[c_ptr].addr()
            &&
            perms@[c_ptr].value().parent =~= old(perms)@[c_ptr].value().parent
            &&
            perms@[c_ptr].value().parent_rev_ptr =~= old(perms)@[c_ptr].value().parent_rev_ptr
            &&
            perms@[c_ptr].value().children =~= old(perms)@[c_ptr].value().children
            &&
            perms@[c_ptr].value().depth =~= old(perms)@[c_ptr].value().depth
            &&
            perms@[c_ptr].value().uppertree_seq =~= old(perms)@[c_ptr].value().uppertree_seq
            // &&
            // perms@[c_ptr].value().subtree_set =~= old(perms)@[c_ptr].value().subtree_set
            &&
            perms@[c_ptr].value().root_process =~= old(perms)@[c_ptr].value().root_process
            &&
            perms@[c_ptr].value().owned_procs =~= old(perms)@[c_ptr].value().owned_procs
            &&
            perms@[c_ptr].value().owned_endpoints =~= old(perms)@[c_ptr].value().owned_endpoints
            &&
            perms@[c_ptr].value().owned_threads =~= old(perms)@[c_ptr].value().owned_threads
            &&
            perms@[c_ptr].value().quota =~= old(perms)@[c_ptr].value().quota
            // &&
            // perms@[c_ptr].value().mem_used =~= old(perms)@[c_ptr].value().mem_used
            &&
            perms@[c_ptr].value().owned_cpus =~= old(perms)@[c_ptr].value().owned_cpus
            &&
            perms@[c_ptr].value().scheduler =~= old(perms)@[c_ptr].value().scheduler
            &&
            perms@[c_ptr].value().can_have_children =~= old(perms)@[c_ptr].value().can_have_children,
        forall|c_ptr:ProcPtr| 
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger perms@[c_ptr].value().subtree_set]
            #![trigger old(perms)@[c_ptr].value().subtree_set]
            uppertree_seq@.contains(c_ptr)
            ==>               
            perms@[c_ptr].value().subtree_set@ =~= old(perms)@[c_ptr].value().subtree_set@.insert(new_container_ptr),
        perms@[new_container_ptr].value().subtree_set =~= old(perms)@[new_container_ptr].value().subtree_set,
{}

}