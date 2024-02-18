//! Paging.

use core::ffi::c_void;
use core::mem::{self, MaybeUninit};
use core::ptr;

use bit_field::BitField;

use crate::memory::PhysicalAllocator;

const LEVEL_MASK: u64 = 0b1_1111_1111;

/// The number of bits in a physical address.
///
/// This is also called M in the Intel manual.
const MAXPHYADDR: u64 = 56;

/// The number of bits to represent offsets in a 4KiB page.
const PAGE_SHIFT: u64 = 12;

/// The size of a regular 4KiB page.
const PAGE_SZ: u64 = 4096;

/// Bitmask to get the page in a linear address.
const PAGE_MASK: u64 = !(PAGE_SZ - 1);

/// Bitmask to get the physical address.
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;

/// Bitmask to get the physical page address.
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

pub struct AddressSpace<'a, A: PhysicalAllocator> {
    pml4: *mut PageTable,
    allocator: &'a mut A,
}

#[repr(transparent)]
struct PageTable {
    entries: [MaybeUninit<Entry>; 512],
}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct Entry(u64);

impl<'a, A: PhysicalAllocator> AddressSpace<'a, A> {
    pub fn new(allocator: &'a mut A) -> Self {
        Self {
            pml4: unsafe { Self::allocate_page_table(allocator) },
            allocator,
        }
    }

    pub fn pml4(&self) -> *const c_void {
        self.pml4 as *const _
    }

    pub unsafe fn map(&mut self, vaddr: u64, paddr: u64, user: bool) {
        //log::info!("Mapping VA 0x{:x} -> PA 0x{:x}", vaddr, paddr);

        let mut cur = self.pml4;

        if vaddr as u64 & (1u64 << PAGE_SHIFT - 1) != 0 {
            panic!("vaddr is unaligned");
        }
        if paddr as u64 & (1u64 << PAGE_SHIFT - 1) != 0 {
            panic!("paddr is unaligned");
        }

        for level in 0..3 {
            let index = Self::index(vaddr, level);
            let mut entry = (*cur).read(index);

            if !entry.present() {
                let new_table = Self::allocate_page_table(&mut self.allocator);

                entry = Entry::new()
                    .with_present(true)
                    .with_read_write(true)
                    .with_address(new_table as u64)
                    .with_user(user);
                (*cur).write(index, entry);
            }

            if entry.page_size_bit() {
                unimplemented!("Huge page not implemented");
            }

            cur = entry.address() as *mut PageTable;
        }

        let index = Self::index(vaddr, 3);
        let entry = Entry::new()
            .with_present(true)
            .with_read_write(true)
            .with_address(paddr)
            .with_user(user);

        //log::info!("Physical Mask: 0b{:b}", PHYSICAL_PAGE_MASK);
        //log::info!("Entry: 0b{:b}", entry.0);
        (*cur).write(index, entry);
    }

    unsafe fn allocate_page_table(allocator: &mut A) -> *mut PageTable {
        let table = {
            allocator.allocate_physical(mem::size_of::<PageTable>()).0
        } as *mut PageTable;

        if table as u64 & (1u64 << PAGE_SHIFT - 1) != 0 {
            panic!("Got unaligned page");
        }

        ptr::write_volatile(table, PageTable::zeroed());

        table
    }

    fn index(address: u64, level: usize) -> usize {
        match level {
            0 => ((address >> 39) & LEVEL_MASK) as usize,
            1 => ((address >> 30) & LEVEL_MASK) as usize,
            2 => ((address >> 21) & LEVEL_MASK) as usize,
            3 => ((address >> 12) & LEVEL_MASK) as usize,
            _ => panic!("Invalid level"),
        }
    }
}

impl PageTable {
    const fn zeroed() -> Self {
        unsafe {
            mem::transmute(MaybeUninit::<Self>::zeroed())
        }
    }

    unsafe fn read(&self, index: usize) -> Entry {
        ptr::read_volatile(self.entry(index))
    }

    unsafe fn write(&self, index: usize, value: Entry) {
        //log::info!("writing to 0x{:x?}", self.entry(index));
        ptr::write_unaligned(self.entry(index), value)
    }

    const fn entry(&self, index: usize) -> *mut Entry {
        self.entries[index].as_ptr() as *mut Entry
    }
}

impl Entry {
    const fn new() -> Self {
        Self(0)
    }

    fn present(&self) -> bool {
        (self.0 & 0b1) == 1
    }

    fn address(&self) -> u64 {
        PHYSICAL_PAGE_MASK & self.0
    }

    fn page_size_bit(&self) -> bool {
        self.0.get_bit(7)
        //(self.0 & (1 << 7)) != 0
    }

    fn with_present(mut self, present: bool) -> Self {
        self.0 = (self.0 & !(0b1)) | (if present { 1 } else { 0 });
        self
    }

    fn with_read_write(mut self, read_write: bool) -> Self {
        self.0.set_bit(1, read_write);
        self
    }

    fn with_user(mut self, user: bool) -> Self {
        self.0.set_bit(2, user);
        self
    }

    fn with_address(mut self, address: u64) -> Self {
        let masked = PHYSICAL_PAGE_MASK & address;
        self.0 = self.0 & !(PHYSICAL_PAGE_MASK) | masked;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_level_index() {
        let address: u64 = 0x7f2ec7045000;
        assert_eq!(AddressSpace::index(address, 0), 0xfe);
        assert_eq!(AddressSpace::index(address, 1), 0xbb);
        assert_eq!(AddressSpace::index(address, 2), 0x38);
        assert_eq!(AddressSpace::index(address, 3), 0x45);
    }
}
