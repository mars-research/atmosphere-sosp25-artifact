// Begin verus_shim support

#[cfg(not(verus_shim))]
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[cfg(verus_shim)]
use verus_shim as verus;

#[allow(dead_code)]
fn main() {}

// End verus_shim support

builtin_macros::verus! {

pub fn quadruple(n: usize) -> (result: usize)
    requires n < usize::MAX / 4
    ensures result == 4 * n
{
    n + n + n + n
}

} // verus!
