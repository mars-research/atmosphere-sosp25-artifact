//! Syscalls.

use core::arch::asm;

use asys::MAX_SYSCALLS;
use x86::segmentation::SegmentSelector;
use x86::{msr, Ring};

use crate::gdt::GlobalDescriptorTable;
use crate::interrupt::Registers;
use crate::kernel;

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

static mut SYSCALLS: [u64; MAX_SYSCALLS] = [0; MAX_SYSCALLS];

static mut CPU0_SYSCALL_STACK: [u8; 4 * 1024 * 1024] = [0; 4 * 1024 * 1024];
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
    let star = ((kernel_seg.bits() as u64) << 48)
        | ((user_seg.bits() as u64) << 32)
        | (SYSCALL32_ENTRY_EIP as u64);
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

    SYSCALLS[asys::__NR_PRINT] = sys_print as u64;
    SYSCALLS[asys::__NR_MMAP] = kernel::sys_mmap as u64;
    SYSCALLS[asys::__NR_MRESOLVE] = kernel::sys_resolve as u64;
    SYSCALLS[asys::__NR_NEW_END] = kernel::sys_new_endpoint as u64;
    SYSCALLS[asys::__NR_NEW_PROC] = kernel::sys_new_proc as u64;
    SYSCALLS[asys::__NR_NEW_PROC_W_IO] = kernel::sys_new_proc_with_iommu as u64;
    SYSCALLS[asys::__NR_NEW_THREAD] = kernel::sys_new_thread as u64;
    SYSCALLS[asys::__NR_SEND_EMPTY_NW] = kernel::sys_send_empty_no_wait as u64;
    SYSCALLS[asys::__NR_LOG] = sys_log as u64;
    SYSCALLS[asys::__NR_SEND_EMPTY] = kernel::sys_send_empty as u64;
    SYSCALLS[asys::__NR_RECEIVE_EMPTY] = kernel::sys_receive_empty as u64;
}

// Syscall ABI
//
// Register | User           | Kernel Handler
// ------------------------------------------
// rax      | Syscall Number | Return Value
// rdi      | Arg #1         | Arg #1
// rsi      | Arg #2         | Arg #2
// rdx      | Arg #3         | Arg #3
// rcx      | N/A            | Registers (Arg #4)
// r8       | Arg #4         | Arg #5
// r9       | Arg #5         | Arg #6
//
// All caller-saved registers are considered clobbered once invoked
#[naked]
unsafe extern "C" fn sys_entry() -> ! {
    asm!(
        // We may not have a valid rsp
        // rax, r10, r11

        "mov r10, rsp",
        "mov rsp, [rip + {saved_sp}]", // FIXME: per-CPU stack

        // Here we construct the Registers struct and only save
        // a subset of registers
        "push {user_ss}", // ss
        "push r10",       // rsp
        "push r11",       // rflags
        "push {user_cs}", // cs
        "push rcx",       // rip

        // TODO: Optimize
        "push 0",         // rax
        "push 0",         // rdi
        "push 0",         // rsi
        "push 0",         // rdx
        "push 0",         // rcx (taken by original rip)
        "push 0",         // r8
        "push 0",         // r9
        "push 0",         // r10 (taken by original rsp)
        "push 0",         // r11 (taken by original rflags across syscall)

        "push rbx",       // rbx
        "push rbp",       // rbp
        "push r12",       // r12
        "push r13",       // r13
        "push r14",       // r14
        "push r15",       // r15

        "mov rcx, rsp",

        "cmp rax, {max_syscalls}",
        "jae 2f",

        // In-range syscall
        "shl rax, 3",
        "lea r11, [rip + {syscalls}]",
        "add r11, rax",
        "mov r11, [r11]",
        "cmp r11, 0",
        "jz 2f",

        // handler(arg1, arg2, arg3, registers, arg4, arg5)
        // rdi, rsi, rdx, (rcx), r8, r9
        "call r11",

        "jmp 3f",

        // Invalid syscall
        "2:",
        "mov rax, -1",

        // Cleanup
        "3:",

        // Two cases:
        // 1. Return to the same thread or another thread that was suspended due to a syscall
        //    ("clean" thread)
        // 2. Switch to a different preempted thread
        //
        // For 1, we can directly skip over restoring most registers since
        // we trust the handler to have already restored callee-saved registers
        //
        // TODO: Clear registers?

        // 1. Return to a clean thread
        // Fast return that clobbers rcx, r11

        //"add rsp, 120", // skip r15~rax (15 registers)
        //"pop rcx", // rip
        //"add rsp, 8", // cs
        //"pop r11", // rflags
        //"pop rsp", // rsp
        //"sysretq",

        // 2. Switch to a preempted thread (slow)
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rcx",
        "pop rdx",
        "pop rsi",
        "pop rdi",
        "pop rax",
        "iretq",

        user_ss = const GlobalDescriptorTable::USER_SS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        saved_sp = sym CPU0_SYSCALL_SP,
        max_syscalls = const MAX_SYSCALLS,
        syscalls = sym SYSCALLS,
        options(noreturn),
    );
}

extern "C" fn sys_print(data: *const u8, len: usize, _: usize, regs: &mut Registers) -> isize {
    let s = unsafe {
        let slice = core::slice::from_raw_parts(data, len);
        core::str::from_utf8_unchecked(slice)
    };
    log::info!("print: {}", s);
    0
}

extern "C" fn sys_log(data: *const u8, len: usize, level: log::Level) -> isize {
    let s = unsafe {
        let slice = core::slice::from_raw_parts(data, len);
        core::str::from_utf8_unchecked(slice)
    };
    log::log!(level, "{}", s);
    0
}
