use vstd::prelude::*;

verus! {
/// Registers passed to the ISR.
#[repr(C)]
pub struct PtRegs {
    /*
     * C ABI says these regs are callee-preserved. They aren't saved on kernel entry
     * unless syscall needs a complete, fully filled "struct pt_regs".
     */
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    /* These regs are callee-clobbered. Always saved on kernel entry. */
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rax: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    /*
     * On syscall entry, this is syscall#. On CPU exception, this is error code.
     * On hw interrupt, it's IRQ number:
     */
    pub orig_ax: u64,
    /* Return frame for iretq */
    pub rip: u64,
    pub rcs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
    /* top of stack page */
}

impl PtRegs {  

    pub open spec fn view(&self) -> PtRegs
    {
        *self
    }

    pub fn set(&mut self, input: &PtRegs)
        ensures
            self@ =~= input@,
    {
        self.r15 = input.r15;
        self.r14 = input.r14;
        self.r13 = input.r13;
        self.r12 = input.r12;
        self.rbp = input.rbp;
        self.rbx = input.rbx;

        self.r11 = input.r11;
        self.r10 = input.r10;
        self.r9 = input.r9;
        self.r8 = input.r8;
        self.rax = input.rax;
        self.rcx = input.rcx;
        self.rdx = input.rdx;
        self.rsi = input.rsi;
        self.rdi = input.rdi;

        self.orig_ax = input.orig_ax;

        self.rip = input.rip;
        self.rcs = input.rcs;
        self.rflags = input.rflags;
        self.rsp = input.rsp;
        self.ss = input.ss;
    
    }

    pub fn new(input: &PtRegs) -> (ret : Self)
        ensures
        ret@ =~= input@,
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
            rax : input.rax,
            rcx : input.rcx,
            rdx : input.rdx,
            rsi : input.rsi,
            rdi : input.rdi,

            orig_ax : input.orig_ax,

            rip : input.rip,
            rcs : input.rcs,
            rflags : input.rflags,
            rsp : input.rsp,
            ss : input.ss,
        };
        ret
    }

}

}