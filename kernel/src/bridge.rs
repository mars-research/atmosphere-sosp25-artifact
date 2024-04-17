use core::arch::asm;

use verified::bridge::{SwitchDecision, TrustedBridge};

pub struct Bridge {}

impl TrustedBridge for Bridge {
    fn set_switch_decision(decision: SwitchDecision) {
        let switch_decision = unsafe {
            &mut *crate::cpu::get_current_cpu_field_ptr!(switch_decision, SwitchDecision)
        };
        *switch_decision = decision;
    }

    fn set_cr3(cr3: u64) {
        unsafe {
            asm!(
                "mov {tmp}, {pcide}",
                "test {tmp}, {tmp}",
                "jnz 2f",

                // Disable PCIDE
                "mov {tmp}, ~(1 << 63)",
                "and {cr3}, {tmp}",

                "2:",
                "mov cr3, {cr3}",
                tmp = out(reg) _,
                cr3 = in(reg) cr3,
                pcide = sym crate::boot::PCIDE,

                options(readonly, nostack),
            );
            // asm!(
            //     "mov cr3, {cr3}",
            //     cr3 = in(reg) cr3,
            // );
        }
    }
}
