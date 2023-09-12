//! Paging.
//!
//! Here we use zero-indexed bit offsets like the Intel manual. Bit 0
//! refers to the least significant bit.

use vstd::prelude::*;
use vstd::ptr::PointsTo;

use crate::page::{PagePPtr, PagePerm};

verus! {

macro_rules! common_entry_impl {
    // Can't rely on the verus macro transformations here
    () => {
        fn new() -> Self {
            let v = 0u64;

            // The present bit is zero
            #[cfg(verus_keep_ghost)]
            assert_bit_vector(#[verifier::spec] {
                // We cannot use v or anything that will be translated into
                // a function call
                0u64 & 0b1u64 == 0
            });

            let s = Self(v);

            // ... so it's not present (obviously)
            #[cfg(verus_keep_ghost)]
            assert_(#[verifier::spec] !s.spec_present());

            s
        }

        #[cfg(verus_keep_ghost)]
        #[verifier::spec]
        #[verus::internal(closed)]
        fn spec_new() -> Self {
            Self(0)
        }

        fn present(&self) -> bool {
            (self.0 & 0b1) == 1
        }

        #[cfg(verus_keep_ghost)]
        #[verifier::spec]
        #[verus::internal(closed)]
        fn spec_present(&self) -> bool {
            (self.0 & 0b1) == 1
        }
    }
}

/*
macro_rules! bits_inclusive {
    ($msb:expr, $lsb:expr) => ({
        let msb_mask = (1u64 << ($msb + 1)) - 1;
        let lsb_mask = !((1u64 << $lsb) - 1);
        msb_mask & lsb_mask
    })
}
*/

macro_rules! extract_9_bits_from {
    ($address:expr, $lsb:expr) => ({
        // Those two are equivalent:
        //
        // - Extract(15, 0, LShR($address, $lsb)) & 0b1_1111_1111
        //     - What we can do from Rust
        // - Concat(zero_pad, Extract($lsb + 8, $lsb, $address))
        //     - How we can directly extract in Z3
        (
            ($address >> $lsb) // LShR($address, $lsb)
            as u16             // Extract(15, 0, ...)
        )
        & 0b1_1111_1111u16
    })
}

/// The number of entries in a table.
const TABLE_SIZE: usize = 512;

/// The number of bits in a physical address.
///
/// This is also called M in the Intel manual.
const MAXPHYADDR: u64 = 56;

/// The number of bits to represent offsets in a 4KiB page.
const PAGE_SHIFT: u64 = 12;

/// The size of a regular 4KiB page.
const PAGE_SIZE: u64 = 4096;

/// Bitmask to get the page in a linear address.
const PAGE_MASK: u64 = !(PAGE_SIZE - 1);

/// Bitmask to get the physical address.
#[verifier(external_body)]
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;

/// Bitmask to get the physical page address.
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

/// A level in the x86-64 paging structure.
///
/// Each level is represented as a mapping from an index to either
/// the next level of the structure or a data page. Currently
/// there are two valid forms:
///
/// - PagingLevel<E, PagingLevel<EE, ET>>
/// - PagingLevel<E, [u8; 4096]>
pub struct PagingLevel<E: Entry, T: MapTarget> {
    pub entries: [E; TABLE_SIZE],

    // maybe a Seq<Option<PagePerm>>?
    pub perms: Ghost<Map<nat, PointsTo<T>>>,
}

/// A PML4.
///
/// In our case, each entry always points to a page directory pointer table.
pub type PML4 = PagingLevel<PML4E, PDPT>;

/// A page directory pointer table.
///
/// In our case, each entry always points to a page directory.
pub type PDPT = PagingLevel<PDPTE, PD>;

/// A page directory.
///
/// In our case, each entry always points to a page table.
pub type PD = PagingLevel<PDE, PT>;

/// A page table.
///
/// In our case, each entry always points a 4 KiB page.
pub type PT = PagingLevel<PTE, [u8; 4096]>;

/// A PML4 entry controlling a 512 GiB region.
///
/// In our case, it always points to a page directory pointer table.
#[repr(transparent)]
pub struct PML4E(u64);

/// A PDPTE entry controlling a 1 GiB region.
///
/// In our case, it always points to a page directory.
#[repr(transparent)]
pub struct PDPTE(u64);

/// A PTE entry controlling a 2 MiB region.
///
/// In our case, it always points to a page table.
#[repr(transparent)]
pub struct PDE(u64);

/// A PTE entry pointing to a 4 KiB page.
#[repr(transparent)]
pub struct PTE(u64);

/// An entry type.
///
/// This can be one of the following:
///
/// - PML4E
/// - PDPTE
/// - PDE
/// - PTE
pub trait Entry: Sized {
    /// Returns a non-present entry.
    #[verifier(when_used_as_spec(spec_new))]
    fn new() -> (ret: Self)
        ensures
            !ret.present(),
            ret == Self::spec_new();

    spec fn spec_new() -> (ret: Self);

    /// Returns whether the entry is well-formed or not.
    ///
    /// Different types have different well-formedness requirements
    /// according to the Intel manual.
    spec fn wf(&self) -> bool;

    /// Returns the index in the table given a linear address.
    ///
    /// Multiple linear addresses can map to the same table index.
    #[verifier(when_used_as_spec(spec_table_index))]
    fn table_index(address: u64) -> (ret: u16)
        ensures
            ret < 512,
            ret == Self::spec_table_index(address);

    spec fn spec_table_index(address: u64) -> (ret: u16);

    /// Returns whether the entry is present.
    #[verifier(when_used_as_spec(spec_present))]
    fn present(&self) -> (ret: bool)
        ensures
            ret == self.spec_present();

    spec fn spec_present(&self) -> bool;

    /// Returns the physical address part of the entry.
    #[verifier(when_used_as_spec(spec_address))]
    fn address(&self) -> (ret: usize)
        requires
            self.wf(),
            self.present(),
        ensures
            ret == self.spec_address();

    spec fn spec_address(&self) -> usize;
}

/// A target of an entry.
///
/// This can be either the next level of the paging structure or
/// a data page.
pub trait MapTarget: Sized {
    /// Returns the set of reachable pages given a typed permission.
    spec fn page_closure_perm(perm: PointsTo<Self>) -> Set<int>;
}

impl<E: Entry, T: MapTarget> PagingLevel<E, T> {
    pub open spec fn wf(&self) -> bool {
        &&& self.wf_perms()
    }

    pub open spec fn wf_perms(&self) -> bool {
        // Each entry being present is equivalent to the permission existing
        forall |i: int| 0 <= i < 512 ==>
            #[trigger] self.entries[i].present() == self.perms@.dom().contains(i as nat)

        // Each permission is associated with the physical address
        && forall |i: int| 0 <= i < 512 ==>
            #[trigger] self.entries[i].present() ==> (self.entries[i].address() == self.perms@[i as nat]@.pptr)
    }

    pub closed spec fn page_closure(&self) -> Set<int> {
        self.perms@.dom().fold(Set::<int>::empty(), |acc: Set::<int>, i: nat| -> Set::<int> {
            acc + MapTarget::page_closure_perm(self.perms@[i])
        })
    }

    /// Inserts a present entry.
    pub fn insert(&mut self, index: u16, entry: E, perm: PointsTo<T>)
        requires
            old(self).wf(),
            !old(self).perms@.dom().contains(index as nat),
            !old(self).entries[index as int].present(),

            index < 512,

            entry.present(),
            entry.wf(),
            entry.address() == perm@.pptr,
        ensures
            self.wf(),
            self.perms@ == old(self).perms@.insert(index as nat, perm),
            self.entries[index as int] == entry,
            self.entries[index as int].present(),
    {
        self.set_entry(index, entry);

        proof {
            assert(self.perms@ == old(self).perms@);
            self.perms@ = self.perms@.insert(index as nat, perm);
        }

        /*
        assert(self.wf()) by {
            assert(!old(self).perms@.dom().contains(index as nat));

            assert(forall |i: int| 0 <= i < 512 ==>
                #[trigger] self.entries[i].present() == self.perms@.dom().contains(i as nat));

            assert(forall |i: int| 0 <= i < 512 ==>
                #[trigger] self.entries[i].present() ==> (self.entries[i].address() == self.perms@[i as nat]@.pptr));
        };
        */
    }

    // Trusted methods

    /// Creates a new mapping level.
    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.entries@ == Seq::new(512, |i: int| E::new()),
            ret.perms@ == Map::<nat, PointsTo<T>>::empty(),

            // TODO
            forall |i: int| 0 <= i < 512 ==>
                !#[trigger] ret.entries[i].present(),
    {
        Self {
            entries: [(); 512].map(|_| {
                E::new()
            }),
            perms: Ghost::assume_new(),
        }
    }

    /// Sets a present entry in the array.
    ///
    /// This neither requires nor bestows well-formedness of the entire
    /// paging level.
    #[verifier(external_body)]
    fn set_entry(&mut self, index: u16, entry: E)
        requires
            // Later uncovered by get_entry()
            entry.wf(),

            index < 512,
        ensures
            // The entry was changed
            self.entries[index as int] == entry,

            // Everything else was unchanged
            forall |i: int|
                0 <= i < 512 && i != index as nat ==> self.entries[i] == old(self).entries[i],

            self.perms@ == old(self).perms@,
    {
        self.entries[index as usize] = entry;
    }

    /// Clears an entry from the array.
    ///
    /// This neither requires nor bestows well-formedness of the entire
    /// paging level.
    #[verifier(external_body)]
    fn clear_entry(&mut self, index: u16)
        requires
            index < 512,
        ensures
            // The entry was changed
            !self.entries[index as int].present(),

            // Everything else was unchanged
            forall |i: int|
                0 <= i < 512 && i != index as nat ==> self.entries[i] == old(self).entries[i],

            self.perms@ == old(self).perms@,
    {
        self.entries[index as usize] = E::new();
    }

    /// Gets an entry from the array.
    ///
    /// This uncovers the entry state for the verifier.
    #[verifier(external_body)] // TODO: wrap array
    pub fn get_entry(&self, index: u16) -> (ret: Option<&E>)
        requires
            self.wf(),

            index < 512,
        ensures
            ret.is_Some() ==> {
                // The entry is present
                &&& self.entries[index as int].present()

                // ... and well-formed (because of set_entry)
                &&& self.entries[index as int].wf()
            },
            ret.is_None() ==> {
                // The entry is absent
                &&& !self.entries[index as int].present()
            },
    {
        let entry = &self.entries[index as usize];

        if entry.present() {
            Some(entry)
        } else {
            None
        }
    }
}

impl MapTarget for [u8; 4096] {
    closed spec fn page_closure_perm(perm: PointsTo<Self>) -> Set<int> {
        Set::empty().insert(perm@.pptr)
    }
}

impl<E: Entry, T: MapTarget> MapTarget for PagingLevel<E, T> {
    closed spec fn page_closure_perm(perm: PointsTo<Self>) -> Set<int>
        // recommends perm@.value.is_Some()
    {
        let level = perm@.value.get_Some_0();
        level.page_closure()
    }
}

impl Entry for PML4E {
    fn address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn spec_address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn wf(&self) -> bool {
        true
    }

    fn table_index(address: u64) -> (ret: u16) {
        let index = extract_9_bits_from!(address, 39u64);
        assert(extract_9_bits_from!(address, 39u64) < 512) by (bit_vector);
        index
    }

    closed spec fn spec_table_index(address: u64) -> (ret: u16) {
        // Bits 47:39 inclusive
        extract_9_bits_from!(address, 39u64)
    }

    common_entry_impl!();
}

impl Entry for PDPTE {
    fn address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn spec_address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn wf(&self) -> bool {
        true
    }

    fn table_index(address: u64) -> (ret: u16) {
        let index = extract_9_bits_from!(address, 30u64);
        assert(extract_9_bits_from!(address, 30u64) < 512) by (bit_vector);
        index
    }

    closed spec fn spec_table_index(address: u64) -> (ret: u16) {
        // Bits 38:30 inclusive
        extract_9_bits_from!(address, 30u64)
    }

    common_entry_impl!();
}

impl Entry for PDE {
    fn address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn spec_address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn wf(&self) -> bool {
        true
    }

    fn table_index(address: u64) -> (ret: u16) {
        let index = extract_9_bits_from!(address, 21u64);
        assert(extract_9_bits_from!(address, 21u64) < 512) by (bit_vector);
        index
    }

    closed spec fn spec_table_index(address: u64) -> (ret: u16) {
        // Bits 29:21 inclusive
        extract_9_bits_from!(address, 21u64)
    }

    common_entry_impl!();
}

impl Entry for PTE {
    fn address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn spec_address(&self) -> usize {
        (self.0 & PHYSICAL_PAGE_MASK) as usize
    }

    closed spec fn wf(&self) -> bool {
        true
    }

    fn table_index(address: u64) -> (ret: u16) {
        let index = extract_9_bits_from!(address, 12u64);
        assert(extract_9_bits_from!(address, 12u64) < 512) by (bit_vector);
        index
    }

    closed spec fn spec_table_index(address: u64) -> (ret: u16) {
        // Bits 12:20 inclusive
        extract_9_bits_from!(address, 12u64)
    }

    common_entry_impl!();
}

impl PTE {
    #[verifier(external_body)]
    fn map(page: PagePPtr) -> (ret: Self)
        requires
            // The page is page-aligned and does not have extra high bits
            page.id() as u64 & PHYSICAL_PAGE_MASK == page.id() as u64,
        ensures
            ret.present(),
            ret.address() == page.id(),
    {
        todo!();
    }
}

mod spec_tests {
    use super::*;

    fn test_page_closure(a: PagePPtr, ap: PagePerm, b: PagePPtr, bp: PagePerm)
        requires
            a.id() == ap@.pptr,
            b.id() == bp@.pptr,
    {
        let mut map = PT::new();

        // The page is page-aligned and does not have extra high bits
        // TODO: This should be guaranteed on the allocator side
        assume(a.id() as u64 & PHYSICAL_PAGE_MASK == a.id() as u64);

        let pte = PTE::map(a);

        map.insert(0, pte, ap);
    }
}

}
