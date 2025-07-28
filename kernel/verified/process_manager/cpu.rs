use vstd::prelude::*;
verus! {

use crate::define::*;

#[derive(Clone, Copy, Debug)]
pub struct Cpu {
    pub owning_container: ContainerPtr,
    pub active: bool,
    pub current_thread: Option<ThreadPtr>,
}

} // verus!
