mod allocator;

use core::num::NonZeroU64;

use crate::elf::Memory;
use astd::heapless::Vec as ArrayVec;

/// A range of memory, denoted by the base address and size.
#[derive(Debug, Clone)]
pub struct MemoryRange {
    base: u64,
    size: NonZeroU64,
}

impl MemoryRange {
    pub fn new(base: u64, size: u64) -> Self {
        Self {
            base,
            size: NonZeroU64::new(size).unwrap(),
        }
    }

    pub const fn base(&self) -> u64 {
        self.base
    }

    pub const fn size(&self) -> u64 {
        self.size.get()
    }

    pub const fn end_inclusive(&self) -> u64 {
        self.base + self.size.get() - 1
    }

    pub const fn intersects(&self, other: &MemoryRange) -> bool {
        (self.base <= other.end_inclusive()) && (self.end_inclusive() >= other.base)
    }

    pub const fn contains(&self, address: u64) -> bool {
        (self.base <= address) && (address <= self.end_inclusive())
    }

    pub const fn fully_contains(&self, other: &MemoryRange) -> bool {
        (self.base <= other.base) && (self.end_inclusive() >= other.end_inclusive())
    }
}

/// Computes a list of usable physical memory regions.
///
/// `memory_regions` is a disjoint list of all physical memory regions.
/// `occupied_regions` is a disjoint list of occupied physical memory regions.
pub fn compute_usable_memory_regions(
    memory_regions: &[MemoryRange],
    occupied_regions: &[MemoryRange],
) -> ArrayVec<MemoryRange, 100> {
    let mut occupied_regions: ArrayVec<MemoryRange, 100> =
        ArrayVec::from_slice(occupied_regions).expect("Too many occupied regions");
    occupied_regions.sort_unstable_by(|a, b| a.base().cmp(&b.base()));

    let mut usable_regions = ArrayVec::new();

    for memory_region in memory_regions.iter() {
        let mut splits: ArrayVec<MemoryRange, 100> = ArrayVec::new();
        let mut remaining = memory_region.clone();

        for occupied in occupied_regions.iter() {
            if !occupied.intersects(&remaining) {
                // disjoint
                continue;
            }

            if occupied.fully_contains(&remaining) {
                // completely occupied, no remaining
                break;
            }

            if remaining.base() < occupied.base() {
                // 1 usable region at the beginning
                splits
                    .push(MemoryRange::new(
                        remaining.base(),
                        occupied.base() - remaining.base(),
                    ))
                    .unwrap();
            }

            if occupied.end_inclusive() < remaining.end_inclusive() {
                remaining = MemoryRange::new(
                    occupied.end_inclusive() + 1,
                    remaining.end_inclusive() - occupied.end_inclusive(),
                );
            } else {
                // nothing remaining
                break;
            }
        }

        usable_regions.extend(splits);
        usable_regions.push(remaining).unwrap();
    }

    usable_regions
}

pub unsafe fn init() {
    if let Some(reserved_region) = crate::boot::get_reserved_region() {
        allocator::init(
            reserved_region.base() as *mut u8,
            reserved_region.size() as usize,
        );
    } else {
        panic!("No region was reserved for the allocator");
    }
}

pub fn memory() -> &'static mut impl Memory {
    unsafe { &mut allocator::ALLOCATOR }
}
