use vstd::prelude::*;

// use crate::proc::*;
use crate::define::*;

use crate::linked_list::*;

verus! {
pub struct Scheduler{
    queue: LinkedList<ThreadPtr>,
}

impl Scheduler{
    pub closed spec fn wf(&self) -> bool{
        self.queue.wf()
    }

    pub closed spec fn view(&self) -> Seq<ThreadPtr>
    {
        self.queue@
    }

    pub closed spec fn page_closure(&self) -> Set<PagePtr>{
        self.queue.page_closure()
    }

    pub closed spec fn node_ref_valid(&self, nr: &NodeRef<ThreadPtr>) -> bool
    {
        self.queue.node_ref_valid(nr)
    }

    pub closed spec fn node_ref_resolve(&self, nr: &NodeRef<ThreadPtr>) -> &ThreadPtr
    {
        self.queue.node_ref_resolve(nr)
    }
}

}