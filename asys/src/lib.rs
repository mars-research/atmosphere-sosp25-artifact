#![no_std]

pub mod logger;

use core::arch::asm;

pub use logger::init_logging;

pub const MAX_SYSCALLS: usize = 64;
pub const __NR_PRINT: usize = 0;

macro_rules! syscall {
    ($nr:expr, $a:expr, $b:expr) => {{
        let ret: isize;
        asm!(
            "syscall",
            inout("rax") $nr => ret,
            inout("rdi") $a => _,
            inout("rsi") $b => _,
            out("rdx") _,
            out("rcx") _,
            out("r8")  _,
            out("r9") _,
            out("r10") _,
            out("r11") _,
        );
        ret
    }}
}

pub unsafe fn sys_print(data: *const u8, len: usize) -> isize {
    syscall!(__NR_PRINT, data, len)
}
