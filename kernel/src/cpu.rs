//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - GDT
//! - TSS
//! - IST stack spaces

use core::arch::asm;
use core::mem::MaybeUninit;
use core::ptr;

use x86::msr;

use verified::trap::Registers;
use crate::interrupt::x86_xapic::XAPIC;
use crate::gdt::{GlobalDescriptorTable, IstStack, TaskStateSegment};
use crate::thread::SwitchDecision;

const NEW_CPU: Cpu = Cpu::new();

/// Per-processor data.
static mut CPUS: [Cpu; 16] = [NEW_CPU; 16];

/// Offset of GS where the CPU ID is located.
const GS_CPU_ID_OFFSET: usize = 8;

macro_rules! read_current_cpu_offset {
    ($offset:expr) => {{
        let value: u64;
        unsafe {
            asm!(
                "mov {result}, gs:[{offset}]",
                offset = const $offset,
                result = out(reg) value,
            );
        }
        value
    }}
}

macro_rules! read_current_cpu_field {
    ($field:ident) => {
        read_current_cpu_offset!(memoffset::offset_of!($crate::cpu::Cpu, $field))
    }
}

macro_rules! get_current_cpu_field_ptr {
    ($field:ident, $type:ty) => {{
        let mut address: u64 = memoffset::offset_of!($crate::cpu::Cpu, $field) as u64;
        #[allow(unused_unsafe)] // nested unsafe
        unsafe {
            asm!(
                "add {result}, gs:{self_offset}",
                self_offset = const memoffset::offset_of!($crate::cpu::Cpu, self_ptr),
                result = inout(reg) address => address,
                options(pure),
            );
        }
        address as *mut $type
    }}
}
pub(crate) use get_current_cpu_field_ptr;

/// Per-processor data for a CPU.
#[repr(C, align(4096))]
pub struct Cpu {
    /// A pointer to ourselves.
    ///
    /// We do a `mov rax, gs:[GS_SELF_PTR_OFFSET]` to get our own address.
    /// We also want to be able to easily access other fields directly.
    pub self_ptr: *const Cpu,

    /// The CPU ID.
    ///
    /// Currently it's the logical APIC ID.
    pub id: usize,

    /// The state of the parked thread.
    pub parked: Registers,

    /// State for the xAPIC driver.
    pub xapic: MaybeUninit<XAPIC>,

    /// The context switch decision upon exiting the kernel.
    pub switch_decision: SwitchDecision,

    /// The Global Descriptor Table.
    ///
    /// See [crate::gdt] for a list of indices and their associated usages.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// The Interrupt Stacks.
    pub ist: [IstStack; 7],
}

unsafe impl Send for Cpu {}
unsafe impl Sync for Cpu {}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            self_ptr: ptr::null(),
            id: 0,
            parked: Registers::zeroed(),
            xapic: MaybeUninit::uninit(),
            switch_decision: SwitchDecision::NoSwitching,
            gdt: GlobalDescriptorTable::empty(),
            tss: TaskStateSegment::new(),
            ist: [
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
            ],
        }
    }
}

/// Returns a handle to the current CPU's data structure.
pub fn get_current() -> &'static mut Cpu {
    let address = read_current_cpu_field!(self_ptr) as *mut Cpu;
    unsafe { &mut *address }
}

/// Returns the current CPU ID.
pub fn get_cpu_id() -> usize {
    read_current_cpu_field!(id) as usize
}

/// Initialize the CPU-local data structure.
///
/// This should only be called once.
pub unsafe fn init_cpu(cpu_id: usize) {
    let mut cpu = &mut CPUS[cpu_id];
    let address = cpu as *const Cpu;

    log::info!("CPU{} @ {:?}", cpu_id, address);

    let self_ptr_ptr = &mut cpu.self_ptr as *mut *const Cpu;
    cpu.self_ptr = address;
    cpu.id = cpu_id;

    msr::wrmsr(msr::IA32_GS_BASE, address as u64);
}
