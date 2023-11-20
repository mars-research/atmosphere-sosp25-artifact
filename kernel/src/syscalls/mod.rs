//! Syscalls.

use x86::segmentation::SegmentSelector;
use x86::{msr, Ring};

use crate::gdt::GlobalDescriptorTable;

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

/// Initializes syscalls.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    use GlobalDescriptorTable as GDT;

    // index - 1 because syscall and sysret will add 8 (cs) or 16 (ss) to those values
    let kernel_seg = SegmentSelector::new(GDT::KERNEL_CODE_INDEX - 1, Ring::Ring0);
    let user_seg = SegmentSelector::new(GDT::USER_CODE_INDEX - 1, Ring::Ring3);

    // Set STAR
    let star = ((kernel_seg.bits() as u64) << 48) | ((user_seg.bits() as u64) << 32) | (SYSCALL32_ENTRY_EIP as u64);
    msr::wrmsr(msr::IA32_STAR, star);

    // Set LSTAR - 64-bit syscall entry
    msr::wrmsr(msr::IA32_LSTAR, sys_entry as *const () as u64);

    // Set LSTAR - 32-bit syscall entry
    msr::wrmsr(msr::IA32_CSTAR, SYSCALL32_ENTRY);

    // Enable EFER Bit 0 - System Call Extensions
    let mut efer = msr::rdmsr(msr::IA32_EFER);
    efer |= 0x1;
    msr::wrmsr(msr::IA32_EFER, efer);
}

pub fn sys_entry() {
    log::info!("sys_entry!");
    loop {}
}
