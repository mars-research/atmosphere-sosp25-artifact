//! Threading.

use core::mem;

use x86::segmentation;

use crate::interrupt::{self, Registers, Cycles};
use crate::cpu;

const TIME_SLICE: Cycles = Cycles(1_000_000);

/// Starts a thread.
pub unsafe fn start_thread(code: u64, stack: u64) {
    log::info!("Starting thread code={:#x} stack={:#x}", code, stack);

    let cpu = cpu::get_current();
    let mut regs = Registers::zeroed();

    regs.rip = code;
    regs.rsp = stack;
    regs.cs = segmentation::cs().bits() as u64;
    regs.ss = segmentation::ss().bits() as u64;
    regs.flags = 1 << 9; // Interrupt Enable

    cpu.parked = regs;

    interrupt::set_timer(TIME_SLICE);
}

/// Schedules the next thread, returning its time slice.
pub fn schedule(regs: &mut Registers) -> Option<Cycles> {
    crate::debugger::breakpoint(1);
    let cpu = cpu::get_current();
    mem::swap(&mut cpu.parked, regs);
    Some(TIME_SLICE)
}
