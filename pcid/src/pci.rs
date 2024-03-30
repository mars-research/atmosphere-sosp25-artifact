pub use crate::bar::PciBar;
pub use crate::bus::{PciBus, PciBusIter};
pub use crate::class::PciClass;
pub use crate::dev::{PciDev, PciDevIter};
pub use crate::header::{PciHeader, PciHeaderError, PciHeaderType};

use core::arch::asm;
pub struct Pci;

impl Pci {
    pub fn new() -> Self {
        Pci
    }

    pub fn buses<'pci>(&'pci self) -> PciIter<'pci> {
        PciIter::new(self)
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub unsafe fn read(&self, bus: u8, dev: u8, func: u8, offset: u8) -> u32 {
        let address = 0x80000000
            | ((bus as u32) << 16)
            | ((dev as u32) << 11)
            | ((func as u32) << 8)
            | ((offset as u32) & 0xFC);
        let value: u32;

        asm!("mov dx, 0xCF8
              out dx, eax
              mov dx, 0xCFC
              in eax, dx",
              inout("eax") address => value, options(nostack, nomem, preserves_flags));
        value
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub unsafe fn write(&self, bus: u8, dev: u8, func: u8, offset: u8, value: u32) {
        let address = 0x80000000
            | ((bus as u32) << 16)
            | ((dev as u32) << 11)
            | ((func as u32) << 8)
            | ((offset as u32) & 0xFC);
        asm!("mov dx, 0xCF8
              out dx, eax",
              in("eax") address, options(nostack, nomem, preserves_flags));
        asm!("mov dx, 0xCFC
              out dx, eax",
              in("eax") value, options(nostack, nomem, preserves_flags));
    }
}

pub struct PciIter<'pci> {
    pci: &'pci Pci,
    num: u32,
}

impl<'pci> PciIter<'pci> {
    pub fn new(pci: &'pci Pci) -> Self {
        PciIter { pci: pci, num: 0 }
    }
}

impl<'pci> Iterator for PciIter<'pci> {
    type Item = PciBus<'pci>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.num < 255 {
            /* TODO: Do not ignore 0xFF bus */
            let bus = PciBus {
                pci: self.pci,
                num: self.num as u8,
            };
            self.num += 1;
            Some(bus)
        } else {
            None
        }
    }
}
