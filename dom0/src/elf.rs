use x86::current::paging::{VAddr, PAddr};

use aelf::{VirtualMapper, ContiguousMapping};
use astd::memory::PageProtection;

pub struct Mapper {
    base: usize,
}

impl Mapper {
    pub fn new(base: usize) -> Self {
        Self {
            base,
        }
    }
}

impl VirtualMapper for Mapper {
    unsafe fn map_anonymous(
            &mut self,
            base: VAddr,
            size: usize,
            protection: PageProtection,
        ) -> ContiguousMapping {
        if base.0 != 0 {
            return ContiguousMapping {
                vaddr: base,
                paddr: PAddr(base.0),
            };
        }

        if size % 4096 != 0 {
            panic!("Size {} is not aligned", size);
        }

        match asys::sys_mmap(self.base, 0x0000_0000_0000_0002u64 as usize, size / 4096) {
            0 => {
                ContiguousMapping {
                    vaddr: VAddr(self.base as u64),
                    paddr: PAddr(self.base as u64),
                }
            }
            _ => {
                panic!("sys_mmap failure");
            }
        }
    }
}
