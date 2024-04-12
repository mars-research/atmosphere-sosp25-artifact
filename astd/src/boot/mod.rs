//! Boot manager handoff.

use core::ffi::c_void;
use core::ptr;

use crate::heapless::Vec as ArrayVec;
use crate::string::ArrayString;

/// The type of physical memory.
///
/// This is a simplified version of `BootMemoryType` in aloader.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum PhysicalMemoryType {
    /// Used by the kernel.
    Kernel,

    /// Used by page tables.
    PageTable,

    /// Used by a domain.
    Domain,

    /// Available to be allocated.
    Available,

    /// Reserved for other use.
    Reserved,
}

/// Boot manager handoff information.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct BootInfo {
    /// The kernel command line.
    pub command_line: ArrayString<4096>,

    /// The page table.
    pub pml4: *const c_void,

    /// The initial domain.
    pub dom0: Option<DomainMapping>,

    /// The payload mapped into dom0.
    pub payload: Option<Payload>,

    /// All available physical pages and their state.
    pub pages: ArrayVec<(u64, PhysicalMemoryType), { 4 * 1024 * 1024 }>,

    /// Whether Tagged TLB is enabled.
    pub pcide: bool,
}

/// A loaded domain.
///
/// The loader only loads and relocates the ELF in identity-mapped memory.
/// The kernel is responsible for setting up everything else.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct DomainMapping {
    /// The beginning of the contiguous reserved space (physical).
    pub reserved_start: *mut u8,

    /// The size of the reserved space.
    pub reserved_size: usize,

    /// The beginning of the virtual address.
    pub virt_start: *mut u8,

    /// The load bias of the domain.
    ///
    /// load_addr = load_bias + vaddr
    pub load_bias: usize,

    /// The entry point.
    pub entry_point: *const c_void,
}

/// A payload.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Payload {
    /// The beginning of the binary in virtual memory.
    pub base: *mut u8,

    /// The size of the binary.
    pub size: usize,
}

impl BootInfo {
    /// Creates an empty BootInfo struct.
    pub const fn empty() -> Self {
        Self {
            command_line: ArrayString::empty(),
            dom0: None,
            payload: None,
            pml4: ptr::null(),
            pages: ArrayVec::new(),
            pcide: false,
        }
    }
}
