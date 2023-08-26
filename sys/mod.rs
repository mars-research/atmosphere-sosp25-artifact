#![no_std]
#![feature(lang_items)]
use core::panic::PanicInfo;

#[verifier::external]
#[panic_handler]
fn handle(_x: &PanicInfo) -> ! {
    loop {}
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

use builtin_macros::*;
use builtin::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::ptr::*;
// mod proc;
mod mem;
mod mars_staticlinkedlist;
mod mars_array;
mod mars_linkedlist;
// mod mars_resizearr;
// mod mars_array_node;
use mars_array::MarsArray;
use mars_staticlinkedlist::MarsStaticLinkedList;
// use proc::ProcessManager;
// use mars_resizearr::MarsResizeArray;
// use mars_array_node::MarsNoderrayNode;

pub type Index = isize;
pub type PageMemPPtr = usize;

pub const NULL_POINTER: usize = 0;

pub struct Node{
    pub value:usize,
    pub next:Index,
    pub prev:Index,
}

verus! {
    fn main(){
        
    }
}
