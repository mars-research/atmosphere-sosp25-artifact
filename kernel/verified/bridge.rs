pub trait TrustedBridge {
    fn set_switch_decision(decision: SwitchDecision);
    fn set_cr3(cr3: u64);
    fn set_iommu_pt(bus: usize, device: usize, function: usize, pml4: u64);
}

#[derive(Debug)]
#[repr(u8)]
pub enum SwitchDecision {
    /// The kernel will return to the same thread.
    NoSwitching = 0,

    /// The kernel will switch to a clean thread.
    ///
    /// Clean means it entered the kernel through a syscall.
    SwitchToClean = 1,

    /// The kernel will switch to a clean thread.
    SwitchToPreempted = 2,
}
