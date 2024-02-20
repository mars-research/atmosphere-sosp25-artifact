use vstd::prelude::*;
verus!{

// #[verifier(external_body)]
// pub fn page_to_iommutable(page1: (PagePPtr,Tracked<PagePerm>), ) -> (ret :(PPtr::<IO>, Tracked<PointsTo<Process>>))
//     requires page.0.id() == page.1@@.pptr,
//             page.1@@.value.is_Some(),
//     ensures ret.0.id() == ret.1@@.pptr,
//             ret.0.id() == page.0.id(),
//             ret.1@@.value.is_Some(),
//             ret.1@@.value.get_Some_0().owned_threads.arr_seq@.len() == MAX_NUM_THREADS_PER_PROC,
// {
//     (PPtr::<Process>::from_usize(page.0.to_usize()), Tracked::assume_new())
// }

}