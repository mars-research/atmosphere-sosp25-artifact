//! Boot manager handoff.

use core::ffi::c_void;

use crate::string::ArrayString;

/// Boot manager handoff information.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct BootInfo {
    /// The kernel command line.
    pub command_line: ArrayString<4096>,

    /// The initial domain.
    pub dom0: Option<DomainMapping>,
}

/// A loaded domain.
///
/// The loader only loads and relocates the ELF in identity-mapped memory.
/// The kernel is responsible for setting up everything else.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct DomainMapping {
    /// The beginning of the contiguous reserved space.
    pub reserved_start: *mut u8,

    /// The size of the reserved space.
    pub reserved_size: usize,

    /// The load bias of the domain.
    ///
    /// load_addr = load_bias + vaddr
    pub load_bias: usize,

    /// The entry point.
    pub entry_point: *const c_void,

    /// The page table.
    pub pml4: *const c_void,
}

impl BootInfo {
    /// Creates an empty BootInfo struct.
    pub const fn empty() -> Self {
        Self {
            command_line: ArrayString::empty(),
            dom0: None,
        }
    }
}
