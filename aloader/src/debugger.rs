//! Debugger integration.

use astd::heapless::Vec as ArrayVec;

#[no_mangle]
#[used]
pub static mut LOADED_BINARIES: ArrayVec<LoadedBinary, 10> = ArrayVec::new();

#[derive(Debug, Clone)]
#[allow(dead_code)] // Read by GDB
pub struct LoadedBinary {
    name: &'static str,
    offset: usize,
}

pub fn add_binary(name: &'static str, offset: usize) {
    let binary = LoadedBinary { name, offset };

    unsafe {
        LOADED_BINARIES.push(binary).expect("Too many binaries");
    }
}
