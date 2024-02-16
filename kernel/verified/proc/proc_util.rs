use core::mem::MaybeUninit;

use vstd::prelude::*;
verus!{
use vstd::ptr::{
    PPtr, PointsTo,
    // PAGE_SZ,
};
use crate::proc::*;

use crate::define::*;

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
    unsafe{(*uptr).assume_init_mut().owned_threads.init();}
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
    unsafe{(*uptr).assume_init_mut().pl_rf = pl_rf;}
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
        proc_perm@@.value.get_Some_0().ioid =~= old(proc_perm)@@.value.get_Some_0().ioid,
        proc_perm@@.value.get_Some_0().pcid =~= pcid,
{
    let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
    unsafe{(*uptr).assume_init_mut().pcid = pcid;}
}

#[verifier(external_body)]
pub fn proc_set_ioid(proc_pptr: PPtr::<Process>,proc_perm: &mut Tracked<PointsTo<Process>>, ioid: Option<IOid>)
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
        proc_perm@@.value.get_Some_0().pcid =~= old(proc_perm)@@.value.get_Some_0().pcid,
        // proc_perm@@.value.get_Some_0().ioid =~= old(proc_perm)@@.value.get_Some_0().ioid,
        proc_perm@@.value.get_Some_0().ioid =~= ioid,
{
    let uptr = proc_pptr.to_usize() as *mut MaybeUninit<Process>;
    unsafe{(*uptr).assume_init_mut().ioid = ioid;}
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
        proc_perm@@.value.get_Some_0().ioid =~= old(proc_perm)@@.value.get_Some_0().ioid,
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
    unsafe{return (*uptr).assume_init_mut().owned_threads.push(thread_ptr);}
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
        proc_perm@@.value.get_Some_0().ioid =~= old(proc_perm)@@.value.get_Some_0().ioid,
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
    unsafe{return (*uptr).assume_init_mut().owned_threads.remove(rf);}
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
        proc_perm@@.value.get_Some_0().ioid =~= old(proc_perm)@@.value.get_Some_0().ioid,
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
    unsafe{return (*uptr).assume_init_mut().owned_threads.pop();}
}

}