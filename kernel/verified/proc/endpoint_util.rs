use core::mem::MaybeUninit;

use vstd::prelude::*;
verus! {
use vstd::ptr::{
    PPtr, PointsTo,
    // PAGE_SZ,
};
use crate::proc::*;

use crate::define::*;

use crate::mars_staticlinkedlist::*;

#[verifier(external_body)]
pub fn endpoint_set_queue_state(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, queue_state: EndpointState)
    requires
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue =~= old(endpoint_perm)@@.value.get_Some_0().queue,
        // endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@,
        endpoint_perm@@.value.get_Some_0().rf_counter=~= old(endpoint_perm)@@.value.get_Some_0().rf_counter,
        endpoint_perm@@.value.get_Some_0().queue_state == queue_state

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    unsafe{(*uptr).assume_init_mut().queue_state = queue_state;}
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
    unsafe{(*uptr).assume_init_mut().rf_counter = (*uptr).assume_init_mut().rf_counter - 1;}
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
    unsafe{(*uptr).assume_init_mut().rf_counter = (*uptr).assume_init_mut().rf_counter + 1;}
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
    unsafe{let ret = (*uptr).assume_init_mut().queue.pop();

    return ret;}
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
    unsafe{let ret = (*uptr).assume_init_mut().queue.push(thread_ptr);

    return ret;}
}

#[verifier(external_body)]
pub fn page_to_endpoint(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Endpoint>, Tracked<PointsTo<Endpoint>>))
    requires page.0.id() == page.1@@.pptr,
            page.1@@.value.is_Some(),
    ensures ret.0.id() == ret.1@@.pptr,
            ret.0.id() == page.0.id(),
            ret.1@@.value.is_Some(),
            ret.1@@.value.get_Some_0().queue.wf(),
            ret.1@@.value.get_Some_0().queue@ =~= Seq::empty(),
            ret.1@@.value.get_Some_0().rf_counter =~= 0,
            ret.1@@.value.get_Some_0().queue_state == true,
            ret.1@@.value.get_Some_0().owning_threads@ =~= Set::empty(),
{
    let uptr = page.0.to_usize() as *mut MaybeUninit<Endpoint>;
    unsafe{
        (*uptr).assume_init_mut().queue.init();
        (*uptr).assume_init_mut().rf_counter = 0;
        (*uptr).assume_init_mut().queue_state = true;
    }

    (PPtr::<Endpoint>::from_usize(page.0.to_usize()), Tracked::assume_new())
}

}
