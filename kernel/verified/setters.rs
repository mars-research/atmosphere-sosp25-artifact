///This file contains all the shitty looking hand written setters that will drive people crazy. 
//TODO: @Xiangdong Send all these seters to a different file and @Zhaofeng can write same macro.

use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    // PAGE_SIZE,
};
use crate::proc::*;

use crate::define::*;

verus!{

// use crate::linked_list::*;

// use crate::pcid_alloc::PCID_MAX;
// use crate::sched::{Scheduler};
// use crate::mars_array::MarsArray;
use crate::mars_staticlinkedlist::*;

#[verifier(external_body)]
pub fn page_to_proc(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Process>, Tracked<PointsTo<Process>>))
    requires page.0.id() == page.1@@.pptr,
            page.1@@.value.is_Some(),
    ensures ret.0.id() == ret.1@@.pptr,
            ret.0.id() == page.0.id(),
            ret.1@@.value.is_Some(),
            ret.1@@.value.get_Some_0().owned_threads.arr_seq@.len() == MAX_NUM_THREADS_PER_PROC,
{
    (PPtr::<Process>::from_usize(page.0.to_usize()), Tracked::assume_new())
}

#[verifier(external_body)]
pub fn page_to_thread(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Thread>, Tracked<PointsTo<Thread>>))
    requires page.0.id() == page.1@@.pptr,
            page.1@@.value.is_Some(),
    ensures ret.0.id() == ret.1@@.pptr,
            ret.0.id() == page.0.id(),
            ret.1@@.value.is_Some(),
            ret.1@@.value.get_Some_0().endpoint_descriptors.wf(),
            ret.1@@.value.get_Some_0().endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {0}),
            ret.1@@.value.get_Some_0().ipc_payload.wf(),
            ret.1@@.value.get_Some_0().ipc_payload.message@ =~= Seq::new(IPC_MESSAGE_LEN as nat, |i:int| {0}),
            ret.1@@.value.get_Some_0().ipc_payload.page_payload@ =~= (0,0),
            ret.1@@.value.get_Some_0().ipc_payload.endpoint_payload =~= None,
{
    let uptr = page.0.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().endpoint_descriptors.init2zero();
    (*uptr).assume_init_mut().ipc_payload.message.init2zero();
    (*uptr).assume_init_mut().ipc_payload.page_payload = (0,0);
    (*uptr).assume_init_mut().ipc_payload.endpoint_payload = None;
    (PPtr::<Thread>::from_usize(page.0.to_usize()), Tracked::assume_new())
}

#[verifier(external_body)]
pub fn proc_to_page(proc: (PPtr::<Process>, Tracked<PointsTo<Process>>)) -> (ret :(PagePPtr,Tracked<PagePerm>))
    requires proc.0.id() == proc.1@@.pptr,
             proc.1@@.value.is_Some(),
    ensures ret.0.id() == ret.1@@.pptr,
            ret.0.id() == proc.0.id(),
            ret.1@@.value.is_Some(),
{
    (PagePPtr::from_usize(proc.0.to_usize()), Tracked::assume_new())
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
pub fn proc_remove_thread(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>, rf: Index) -> (ret: ThreadPtr)
    requires 
        proc_pptr.id() == old(proc_perm)@@.pptr,
        old(proc_perm)@@.value.is_Some(),
        old(proc_perm)@@.value.get_Some_0().owned_threads.wf(),
        old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(rf),
        old(proc_perm)@@.value.get_Some_0().owned_threads.unique(),
    ensures
        proc_pptr.id() == proc_perm@@.pptr,
        proc_perm@@.value.is_Some(),
        proc_perm@@.value.get_Some_0().owned_threads.wf(),
        //proc_perm@@.value.get_Some_0().owned_threads =~= old(proc_perm)@@.value.get_Some_0().owned_threads,
        proc_perm@@.value.get_Some_0().pl_rf =~= old(proc_perm)@@.value.get_Some_0().pl_rf,
        proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
        proc_perm@@.value.get_Some_0().owned_threads.value_list_len == old(proc_perm)@@.value.get_Some_0().owned_threads.value_list_len - 1,
        ret == old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(rf),
        proc_perm@@.value.get_Some_0().owned_threads.spec_seq@ == old(proc_perm)@@.value.get_Some_0().owned_threads.spec_seq@.remove(old(proc_perm)@@.value.get_Some_0().owned_threads.spec_seq@.index_of(old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(rf))),
        forall| value:usize|  #![auto]  ret != value ==> old(proc_perm)@@.value.get_Some_0().owned_threads.spec_seq@.contains(value) == proc_perm@@.value.get_Some_0().owned_threads.spec_seq@.contains(value),
        proc_perm@@.value.get_Some_0().owned_threads.spec_seq@.contains(ret) == false,
        forall|_index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(_index) && _index != rf ==> proc_perm@@.value.get_Some_0().owned_threads.node_ref_valid(_index),
        forall|_index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(_index) && _index != rf ==> proc_perm@@.value.get_Some_0().owned_threads.node_ref_resolve(_index) == old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(_index),
        proc_perm@@.value.get_Some_0().owned_threads.unique(),

{
    let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
    return (*uptr).assume_init_mut().owned_threads.remove(rf);
}

#[verifier(external_body)]
pub fn proc_pop_thread(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>) -> (ret: ThreadPtr)
    requires 
        proc_pptr.id() == old(proc_perm)@@.pptr,
        old(proc_perm)@@.value.is_Some(),
        old(proc_perm)@@.value.get_Some_0().owned_threads.wf(),
        old(proc_perm)@@.value.get_Some_0().owned_threads.len() != 0,
        old(proc_perm)@@.value.get_Some_0().owned_threads.unique(),
    ensures
        proc_pptr.id() == proc_perm@@.pptr,
        proc_perm@@.value.is_Some(),
        proc_perm@@.value.get_Some_0().owned_threads.wf(),
        //proc_perm@@.value.get_Some_0().owned_threads =~= old(proc_perm)@@.value.get_Some_0().owned_threads,
        proc_perm@@.value.get_Some_0().pl_rf =~= old(proc_perm)@@.value.get_Some_0().pl_rf,
        proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
        proc_perm@@.value.get_Some_0().owned_threads.value_list_len == old(proc_perm)@@.value.get_Some_0().owned_threads.value_list_len - 1,
        ret == old(proc_perm)@@.value.get_Some_0().owned_threads@[0],

        proc_perm@@.value.get_Some_0().owned_threads.spec_seq@ == old(proc_perm)@@.value.get_Some_0().owned_threads.spec_seq@.drop_first(),
        forall| value:usize|  #![auto]  ret != value ==> old(proc_perm)@@.value.get_Some_0().owned_threads.spec_seq@.contains(value) == proc_perm@@.value.get_Some_0().owned_threads.spec_seq@.contains(value),
        proc_perm@@.value.get_Some_0().owned_threads.spec_seq@.contains(ret) == false,
        forall|_index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(_index) && old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(_index) != ret ==> proc_perm@@.value.get_Some_0().owned_threads.node_ref_valid(_index),
        forall|_index:Index| old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_valid(_index) && old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(_index) != ret ==> proc_perm@@.value.get_Some_0().owned_threads.node_ref_resolve(_index) == old(proc_perm)@@.value.get_Some_0().owned_threads.node_ref_resolve(_index),
        proc_perm@@.value.get_Some_0().owned_threads.unique(),

{
    let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
    return (*uptr).assume_init_mut().owned_threads.pop();
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
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
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
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors =~= old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
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
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().parent == parent,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().parent = parent;
}
}

#[verifier(external_body)]
pub fn thread_set_endpoint_descriptors(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, index: usize, endpoint_pointer: EndpointPtr) -> (ret: EndpointPtr)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
            0<=index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            endpoint_descriptors_unique(old(perm)@@.value.get_Some_0().endpoint_descriptors)
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        //perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().endpoint_descriptors.wf(), 
        perm@@.value.get_Some_0().endpoint_descriptors@ =~= old(perm)@@.value.get_Some_0().endpoint_descriptors@.update(index as int, endpoint_pointer),
        ret == old(perm)@@.value.get_Some_0().endpoint_descriptors@[index as int],
        forall|_endpoint_ptr: EndpointPtr| #![auto]  _endpoint_ptr != ret 
            ==> perm@@.value.get_Some_0().endpoint_descriptors@.contains(_endpoint_ptr) == old(perm)@@.value.get_Some_0().endpoint_descriptors@.contains(_endpoint_ptr),
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    let ret = (*uptr).assume_init_mut().endpoint_descriptors.ar[index];
    (*uptr).assume_init_mut().endpoint_descriptors.ar[index] = endpoint_pointer;
    return ret;
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
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().parent_rf == parent_rf,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().parent_rf =parent_rf;
}
}


#[verifier(external_body)]
pub fn thread_set_endpoint_ptr(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, endpoint_ptr: Option<EndpointPtr>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        //perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().endpoint_ptr == endpoint_ptr,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().endpoint_ptr =endpoint_ptr;
    }
}


#[verifier(external_body)]
pub fn thread_set_endpoint_rf(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, endpoint_rf: Option<Index>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        //perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().endpoint_rf == endpoint_rf,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().endpoint_rf =endpoint_rf;
    }
}

#[verifier(external_body)]
pub fn thread_set_error_code(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, error_code: Option<ErrorCodeType>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        //perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().error_code == error_code,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().error_code =error_code;
    }
}

#[verifier(external_body)]
pub fn endpoint_remove_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, rf: Index) -> (ret: ThreadPtr)
    requires 
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().queue.wf(),
        old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(rf),
        old(endpoint_perm)@@.value.get_Some_0().queue.unique(),
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue.wf(),
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@,
        endpoint_perm@@.value.get_Some_0().rf_counter =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().queue.value_list_len == old(endpoint_perm)@@.value.get_Some_0().queue.value_list_len - 1,
        ret == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(rf),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@ == old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.remove(old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.index_of(old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(rf))),
        forall| value:usize|  #![auto]  ret != value ==> old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.contains(value) == endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(value),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(ret) == false,
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && _index != rf ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_valid(_index),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && _index != rf ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_resolve(_index) == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index),
        endpoint_perm@@.value.get_Some_0().queue.unique(),
        // endpoint_perm@@.value.get_Some_0().queue.len() == 0 ==> endpoint_perm@@.value.get_Some_0().state == EMPTY,
        // endpoint_perm@@.value.get_Some_0().queue.len() != 0 ==> endpoint_perm@@.value.get_Some_0().state == old(endpoint_perm)@@.value.get_Some_0().state,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    let ret = (*uptr).assume_init_mut().queue.remove(rf);

    return ret;
}

#[verifier(external_body)]
pub fn endpoint_remove_owning_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, thread_ptr:ThreadPtr)
    requires 
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().owning_threads@.contains(thread_ptr),
        old(endpoint_perm)@@.value.get_Some_0().rf_counter != 0,
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue =~= old(endpoint_perm)@@.value.get_Some_0().queue,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@.remove(thread_ptr),
        endpoint_perm@@.value.get_Some_0().rf_counter as int =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter - 1,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    (*uptr).assume_init_mut().rf_counter = (*uptr).assume_init_mut().rf_counter - 1;
}

#[verifier(external_body)]
pub fn endpoint_add_owning_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, thread_ptr:ThreadPtr)
    requires 
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().owning_threads@.contains(thread_ptr) == false,
        old(endpoint_perm)@@.value.get_Some_0().rf_counter != usize::MAX,
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue =~= old(endpoint_perm)@@.value.get_Some_0().queue,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@.insert(thread_ptr),
        endpoint_perm@@.value.get_Some_0().rf_counter as int =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter + 1,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    (*uptr).assume_init_mut().rf_counter = (*uptr).assume_init_mut().rf_counter + 1;
}

#[verifier(external_body)]
pub fn endpoint_pop_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>) -> (ret: ThreadPtr)
    requires 
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().queue.wf(),
        old(endpoint_perm)@@.value.get_Some_0().queue.unique(),
        old(endpoint_perm)@@.value.get_Some_0().queue.len() != 0,
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue.wf(),
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@,
        endpoint_perm@@.value.get_Some_0().rf_counter =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().queue.value_list_len == old(endpoint_perm)@@.value.get_Some_0().queue.value_list_len - 1,
        ret == old(endpoint_perm)@@.value.get_Some_0().queue@[0],
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@ == old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.drop_first(),
        forall| value:usize|  #![auto]  ret != value ==> old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.contains(value) == endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(value),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(ret) == false,
        old(endpoint_perm)@@.value.get_Some_0().queue@.contains(ret),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index) != ret ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_valid(_index),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index) != ret ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_resolve(_index) == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index),
        endpoint_perm@@.value.get_Some_0().queue.unique(),
        // endpoint_perm@@.value.get_Some_0().queue.len() == 0 ==> endpoint_perm@@.value.get_Some_0().state == EMPTY,
        // endpoint_perm@@.value.get_Some_0().queue.len() != 0 ==> endpoint_perm@@.value.get_Some_0().state == old(endpoint_perm)@@.value.get_Some_0().state,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    let ret = (*uptr).assume_init_mut().queue.pop();

    return ret;
}

#[verifier(external_body)]
pub fn endpoint_push_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, thread_ptr: ThreadPtr) -> (ret: Index)
    requires 
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().queue.wf(),
        old(endpoint_perm)@@.value.get_Some_0().queue.unique(),
        old(endpoint_perm)@@.value.get_Some_0().queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
        old(endpoint_perm)@@.value.get_Some_0().queue@.contains(thread_ptr) == false,
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue.wf(),
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@,
        endpoint_perm@@.value.get_Some_0().rf_counter =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().queue.value_list_len == old(endpoint_perm)@@.value.get_Some_0().queue.value_list_len + 1,
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@ == old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.push(thread_ptr),
        forall| value:usize|  #![auto]  thread_ptr != value ==> old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.contains(value) == endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(value),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(thread_ptr),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_valid(_index),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_resolve(_index) == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) ==> ret != _index,
        endpoint_perm@@.value.get_Some_0().queue.node_ref_valid(ret),
        endpoint_perm@@.value.get_Some_0().queue.node_ref_resolve(ret) == thread_ptr,
        endpoint_perm@@.value.get_Some_0().queue.unique(),
        // endpoint_perm@@.value.get_Some_0().queue.len() == 0 ==> endpoint_perm@@.value.get_Some_0().state == EMPTY,
        // endpoint_perm@@.value.get_Some_0().queue.len() != 0 ==> endpoint_perm@@.value.get_Some_0().state == old(endpoint_perm)@@.value.get_Some_0().state,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    let ret = (*uptr).assume_init_mut().queue.push(thread_ptr);

    return ret;
}

}