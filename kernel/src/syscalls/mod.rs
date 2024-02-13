//! Syscalls.

use core::arch::asm;

use x86::segmentation::SegmentSelector;
use x86::{msr, Ring};

use crate::gdt::GlobalDescriptorTable;

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

static mut CPU0_SYSCALL_STACK: [u8; 4 * 1024 * 1024] = [0; 4 * 1024 * 1024];

#[no_mangle]
static mut CPU0_SYSCALL_SP: u64 = 0;

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

    CPU0_SYSCALL_SP = CPU0_SYSCALL_STACK.as_ptr().add(CPU0_SYSCALL_STACK.len()) as u64;
}

// rax - syscall number
// rdi - arg #1
// rsi - arg #2
// rdx - arg #3
//
// rcx - return address (implicit)
#[naked]
unsafe extern "C" fn sys_entry() -> ! {
    asm!(
        // We may not have a valid rsp
        // rax, r10, r11

        "mov r10, rsp",
        "mov rsp, [rip + CPU0_SYSCALL_SP]", // FIXME: per-CPU stack

        "push r10", // original rsp
        "push rcx", // return address

        "mov rcx, rax",
        "call {handler}",

        "pop rcx",
        "pop rsp",

        "sysretq",

        handler = sym test_sys,
        options(noreturn),
    );
}

extern "C" fn test_sys(a: u64, b: u64, c: u64, num: u64) -> u64 {
    //log::info!("syscall={}, a={}, b={}, c={}", num, a, b, c);

    123
}
