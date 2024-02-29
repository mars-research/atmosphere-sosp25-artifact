use x86::current::paging::{PAddr, VAddr};

use crate::PAGE_SIZE;
use crate::memory::{AddressSpace, PhysicalAllocator, PageProtection, ContiguousMapping, VirtualMapper};

/// The virtual base address userspace programs are loaded to.
pub const USERSPACE_BASE: u64 = 0x8000000000;

pub struct UserspaceMapper<'a, 'b, 'c, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    address_space: &'a mut AddressSpace<'b, PGA>,
    allocator: &'c mut PA,
    phys_base: u64,
}

impl<'a, 'b, 'c, PGA, PA> UserspaceMapper<'a, 'b, 'c, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    pub fn new(address_space: &'a mut AddressSpace<'b, PGA>, allocator: &'c mut PA) -> Self {
        Self {
            address_space,
            allocator,
            phys_base: 0,
        }
    }
}

impl<'a, 'b, 'c, PGA, PA> VirtualMapper for UserspaceMapper<'a, 'b, 'c, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    unsafe fn map_anonymous(
        &mut self,
        base: VAddr,
        size: usize,
        _protection: PageProtection,
    ) -> ContiguousMapping {
        if base.0 != 0 {
            ContiguousMapping {
                vaddr: base,
                paddr: PAddr(base.0 - USERSPACE_BASE + self.phys_base),
            }
        } else {
            let paddr = self.allocator.allocate_physical(size);
            self.phys_base = paddr.0 as u64;

            let phys_base = self.phys_base;
            let virt_base = USERSPACE_BASE;

            let mut cur = phys_base;
            while cur < phys_base + size as u64 {
                unsafe {
                    // Map user view
                    log::info!("vaddr = {:x?}", cur - phys_base + virt_base);
                    self.address_space.map(cur - phys_base + virt_base, cur, true);

                    // Map kernel view (identity)
                    self.address_space.map(cur, cur, false);

                    cur = cur + PAGE_SIZE as u64;
                }
            }

            ContiguousMapping {
                vaddr: VAddr(virt_base),
                paddr,
            }
        }
    }
}

