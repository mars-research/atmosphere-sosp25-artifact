use vstd::prelude::*;
verus! {


/// Registers passed to the ISR.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct PtRegs {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,

    // Original interrupt stack frame

    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl PtRegs {
    pub fn new_empty()-> (ret : Self)
    {
        let ret = Self {
            r15 : 0,
            r14 : 0,
            r13 : 0,
            r12 : 0,
            rbp : 0,
            rbx : 0,
            r11 : 0,
            r10 : 0,
            r9 : 0,
            r8 : 0,
            rcx : 0,
            rdx : 0,
            rsi : 0,
            rdi : 0,
            rax : 0,

            rip : 0,
            cs : 0,
            flags : 0,
            rsp : 0,
            ss : 0,
        };
        ret
    }

    pub fn new(input: &PtRegs) -> (ret : Self)
        ensures
        ret =~= *input,
    {
        let ret = Self {
            r15 : input.r15,
            r14 : input.r14,
            r13 : input.r13,
            r12 : input.r12,
            rbp : input.rbp,
            rbx : input.rbx,

            r11 : input.r11,
            r10 : input.r10,
            r9 : input.r9,
            r8 : input.r8,
            rcx : input.rcx,
            rdx : input.rdx,
            rsi : input.rsi,
            rdi : input.rdi,
            rax : input.rax,

            rip : input.rip,
            cs : input.cs,
            flags : input.flags,
            rsp : input.rsp,
            ss : input.ss,
        };
        ret
    }

}

}
