//! Paging.
//!
//! Here we use zero-indexed bit offsets like the Intel manual. Bit 0
//! refers to the least significant bit.

use vstd::prelude::*;
use vstd::ptr::PointsTo;

use crate::page::{PagePtr, PagePPtr, PagePerm, VAddr, PAddr};
use crate::page_alloc::*;
use crate::mars_array::*;
use crate::page::*;
use crate::pcid_alloc::*;
pub struct AddressSpace(pub PML4);

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

/// A level in the x86-64 paging structure, with linearity enforced for each target.
///
/// Each level is represented as a mapping from an index to either
/// the next level of the structure or a data page. Currently
/// there are three valid forms:
///
/// - `PagingLevel<E, PagingLevel<EE, ET>>`
///     - Example: `type PD = PagingLevel<PDE, PT>`
/// - `PagingLevel<E, [u8; 4096]>`
///     - Example: `type PT = PagingLevel<PTE, [u8; 4096]>`
/// - PagingLevel<E, UntypedPagingLevel<EE>>
///     - `type PD = PagingLevel<PDE, PT>`
///     - `type PT = UntypedPagingLevel<PTE>`
pub struct PagingLevel<E: Entry, T: TableTarget> {
    pub entries: UntypedPagingLevel<E>,

    // maybe a Seq<Option<PagePerm>>?
    pub perms: Ghost<Map<nat, PointsTo<T>>>,
}

/// A level in the x86-64 paging structure.
///
/// This doesn't enforce uniqueness of targets.
pub struct UntypedPagingLevel<E: Entry> {
    pub entries: [E; TABLE_SIZE],
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

//pub type PT = UntypedPagingLevel<PTE>;

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
pub trait TableTarget: Sized {
    /// Returns whether the target is well-formed given a typed permission.
    spec fn wf_perm(perm: PointsTo<Self>) -> bool;

    /// Returns the set of reachable table pages given a typed permission.
    spec fn table_page_closure_perm(perm: PointsTo<Self>) -> Set<int>;

    /// Returns the set of reachable data pages given a typed permission.
    spec fn data_page_closure_perm(perm: PointsTo<Self>) -> Set<int>;
}

impl<E: Entry, T: TableTarget> PagingLevel<E, T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_entries()
        &&& self.wf_recursive()
    }

    pub closed spec fn wf_entries(&self) -> bool {
        // Each entry being present is equivalent to the permission existing
        forall |i: int| 0 <= i < 512 ==>
            #[trigger] self.entries[i].present() == self.perms@.dom().contains(i as nat)

        // Each permission is associated with the physical address
        && forall |i: int| 0 <= i < 512 ==>
            #[trigger] self.entries[i].present() ==>
                (self.entries[i].address() == self.perms@[i as nat]@.pptr)
    }

    pub closed spec fn wf_recursive(&self) -> bool {
        // Each target is well-formed
        forall |i: int| 0 <= i < 512 ==>
            #[trigger] self.entries[i].present() ==> TableTarget::wf_perm(self.perms@[i as nat])
    }

    ///Tmp change @zhaofeng delete this 
    // pub closed spec fn tmp_data_page_closure(&self) -> Set<PagePtr> {
    //     Set::empty()
    // }
    pub open spec fn tmp_wf(&self)->bool{
        &&&
        (forall|va:VAddr| #![auto] self.tmp_get_mem_mappings().dom().contains(va) ==> page_ptr_valid(self.tmp_get_mem_mappings()[va] as usize))

    }

    pub closed spec fn tmp_page_table_page_closure(&self) -> Set<PagePtr> {
        Set::empty()
    }

    pub closed spec fn tmp_get_mem_mappings(&self) -> Map<VAddr,PAddr> {
        Map::empty()
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_va_entry_exists))]
    pub fn va_entry_exists(&self, va:VAddr) -> (ret: bool)
        ensures
            ret == self.va_entry_exists(va),
    {
        arbitrary()
    }


    pub closed spec fn spec_va_entry_exists(&self, va:VAddr) -> bool
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings(),
            page_alloc.wf(),
            self.tmp_page_table_page_closure() =~= old(self).tmp_page_table_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self.va_entry_exists(va) == true,
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn resolve(&self, va:VAddr) -> (ret: Option<PAddr>)
        ensures
            ret.is_None() ==> self.tmp_get_mem_mappings().dom().contains(va) == false,
            ret.is_Some() ==> self.tmp_get_mem_mappings().dom().contains(va) && self.tmp_get_mem_mappings()[va] == ret.unwrap(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn map(&mut self, va:VAddr, pa:PAddr)
        requires
            old(self).wf(),
            old(self).tmp_get_mem_mappings().dom().contains(va) == false,
        ensures
            self.wf(),
            self.tmp_get_mem_mappings().dom().contains(va) == true,
            self.tmp_get_mem_mappings()[va] == pa,
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn unmap(&mut self, va:VAddr) -> (ret: PAddr)
        requires
            old(self).wf(),
            old(self).tmp_get_mem_mappings().dom().contains(va),
        ensures
            self.wf(),
            self.tmp_get_mem_mappings().dom().contains(va) == false,
            old(self).tmp_get_mem_mappings()[va] == ret,
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings().remove(va),
    {
        arbitrary()
    }
    ///end tmp
    
    /// Returns the set of data pages.
    pub closed spec fn data_page_closure(&self) -> Set<int> {
        Set::new(|pptr: int| {
            exists |i: int| 0 <= i < 512 && {
                &&& #[trigger] self.entries[i].present()
                &&& TableTarget::data_page_closure_perm(self.perms@[i as nat]).contains(pptr)
            }
        })
    }

    /// Returns the set of pages that make up the paging structure.
    pub closed spec fn table_page_closure(&self) -> Set<int> {
        Set::new(|pptr: int| {
            exists |i: int| 0 <= i < 512 && {
                &&& #[trigger] self.entries[i].present()
                &&& TableTarget::table_page_closure_perm(self.perms@[i as nat]).contains(pptr)
            }
        })
    }


    /// Returns whether the mapping is at the initial state.
    pub closed spec fn spec_init(&self) -> bool {
        self.perms@ == Map::<nat, PointsTo<T>>::empty()
    }

    /// Inserts a present entry.
    pub fn insert(
        &mut self, // <-- Not possible when nested! Solve inside Untyped
        index: u16,
        entry: E,
        perm: PointsTo<T>,
    )
        requires
            old(self).wf(),

            index < 512,

            // The existing entry must not be present
            !old(self).perms@.dom().contains(index as nat),
            !old(self).entries[index as int].present(),

            // The entry must be present and well-formed
            entry.present(),
            entry.wf(),

            // The typed target must be well-formed
            TableTarget::wf_perm(perm),

            // The entry and the permission must be associated
            entry.address() == perm@.pptr,
        ensures
            self.wf(),
            self.perms@ == old(self).perms@.insert(index as nat, perm),
            self.entries[index as int] == entry,
            self.entries[index as int].present(),
    {
        self.entries.set_entry(index, entry);

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
    pub fn new() -> (ret: Self)
        ensures
            ret.wf(),
            ret.spec_init(),
    {
        let mut ret = Self::init_ghost();

        // ...
        ret.entries = UntypedPagingLevel::new();

        ret
    }

    #[verifier(external_body)]
    fn init_ghost() -> (ret: Self)
        ensures
            ret.perms@ == Map::<nat, PointsTo<T>>::empty(),

            //ret.entries@ == Seq::new(512, |i: int| E::new()),
            //
    {
        Self {
            //entries: [(); 512].map(|_| E::new()),
            entries: UntypedPagingLevel::new(),
            perms: Ghost::assume_new(),
        }
    }
}

impl<E: Entry> UntypedPagingLevel<E> {
    /// Creates a new unchecked mapping level.
    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.entries@ == Seq::new(512, |i: int| E::new()),

            // TODO
            forall |i: int| 0 <= i < 512 ==>
                !#[trigger] ret.entries[i].present(),
    {
        Self {
            entries: [(); 512].map(|_| {
                E::new()
            }),
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_index(&self, i: int) -> E {
        self.entries[i]
    }

    /// Sets a present entry in the array.
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
    {
        self.entries[index as usize] = entry;
    }

    /// Clears an entry from the array.
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
    {
        self.entries[index as usize] = E::new();
    }

    /// Gets an entry from the array.
    ///
    /// This uncovers the entry state for the verifier.
    #[verifier(external_body)] // TODO: wrap array
    pub fn get_entry(&self, index: u16) -> (ret: Option<&E>)
        requires
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

// TableTarget implementations

impl TableTarget for [u8; 4096] {
    closed spec fn wf_perm(perm: PointsTo<Self>) -> bool {
        true
    }

    closed spec fn table_page_closure_perm(perm: PointsTo<Self>) -> Set<int> {
        Set::empty()
    }

    closed spec fn data_page_closure_perm(perm: PointsTo<Self>) -> Set<int> {
        Set::empty().insert(perm@.pptr)
    }
}

impl<E: Entry, T: TableTarget> TableTarget for PagingLevel<E, T> {
    closed spec fn wf_perm(perm: PointsTo<Self>) -> bool {
        let level = perm@.value.get_Some_0();
        level.wf()
    }

    closed spec fn table_page_closure_perm(perm: PointsTo<Self>) -> Set<int>
        // recommends perm@.value.is_Some()
    {
        let level = perm@.value.get_Some_0();
        Set::empty().insert(perm@.pptr) + level.table_page_closure()
    }

    closed spec fn data_page_closure_perm(perm: PointsTo<Self>) -> Set<int>
        // recommends perm@.value.is_Some()
    {
        let level = perm@.value.get_Some_0();
        level.data_page_closure()
    }
}

impl<E: Entry> TableTarget for UntypedPagingLevel<E> {
    closed spec fn wf_perm(perm: PointsTo<Self>) -> bool {
        true
    }

    closed spec fn table_page_closure_perm(perm: PointsTo<Self>) -> Set<int>
        // recommends perm@.value.is_Some()
    {
        Set::empty().insert(perm@.pptr)
    }

    closed spec fn data_page_closure_perm(perm: PointsTo<Self>) -> Set<int>
        // recommends perm@.value.is_Some()
    {
        let level = perm@.value.get_Some_0();

        // Can't look deeper - Just tally up the addresses
        level.entries@.fold_left(Set::<int>::empty(), |acc: Set::<int>, e: E| -> Set::<int> {
            if e.present() {
                acc.insert(e.address() as int)
            } else {
                acc
            }
        })
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
        Self(page.to_usize() as u64 & 0b1)
    }
}

mod spec_tests {
    use super::*;
    use vstd::ptr::PPtr;

    fn test_page_closure(
        a: PagePPtr,
        ap: PagePerm,

        b: PagePPtr,
        bp: PagePerm,

        pd: PPtr<PD>,
        pdp: PointsTo<PD>,
    )
        requires
            a.id() == ap@.pptr,
            b.id() == bp@.pptr,

            pd.id() == pdp@.pptr,
    {
        // All pages are page-aligned and do not have extra high bits
        // TODO: This should be guaranteed on the allocator side
        assume(a.id() as u64 & PHYSICAL_PAGE_MASK == a.id() as u64);
        assume(b.id() as u64 & PHYSICAL_PAGE_MASK == b.id() as u64);
        assume(pd.id() as u64 & PHYSICAL_PAGE_MASK == pd.id() as u64);

        let mut pt = PT::new();

        let pte = PTE::map(a);

        pt.insert(0, pte, ap);

        assert(pt.data_page_closure().contains(ap@.pptr));
        assert(!pt.table_page_closure().contains(ap@.pptr));
    }

    fn test_state_uncovering() {
    }

    fn test_table_index(a: PagePPtr, b: PagePPtr) {
        assume(a.id() == b.id());

        let ai: u16 = PTE::table_index(a.to_usize() as u64);
        let bi: u16 = PTE::table_index(b.to_usize() as u64);
        assert(ai == bi);
    }

    fn test_bitvector_proofs() {
        assert(extract_9_bits_from!(0xffff_1234_5678_9abcu64, 39u64) == 36u16) by (bit_vector);
    }
}

impl MarsArray<AddressSpace,PCID_MAX>{

    #[verifier(external_body)]
    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.tmp_page_table_page_closure() =~= Set::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.tmp_get_mem_mappings() =~= Map::empty(),
    {
        arbitrary()
    }

    // #[verifier(external_body)]
    // pub fn pcid_clear(&mut self, pcid:Pcid, page_alloc :&mut PageAllocator)
    // requires
    //     0<=pcid<PCID_MAX,
    //     old(self).wf(),
    //     old(self)@[pcid as int].0.wf(),
    //     old(page_alloc).wf(),
    // ensures
    //     self.wf(),
    //     self@[pcid as int].0.wf(),
    //     page_alloc.wf(),
    //     self@[pcid as int].0.tmp_page_table_page_closure() =~= Set::empty(),
    //     page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() + old(self)@[pcid as int].0.tmp_page_table_page_closure(),
    //     self@[pcid as int].0.tmp_get_mem_mappings() =~= Map::empty(),
    //     forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
    // {
    //     self.ar[pcid].0.clear(page_alloc);
    // }


    #[verifier(external_body)]
    pub fn pcid_map(&mut self, pcid:Pcid, va:VAddr, pa:PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].0.wf(),
        old(self)@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == false,
    ensures
        self.wf(),
        self@[pcid as int].0.wf(),
        self@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == true,
        self@[pcid as int].0.tmp_get_mem_mappings()[va] == pa,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].0.tmp_get_mem_mappings() =~= old(self)@[pcid as int].0.tmp_get_mem_mappings().insert(va,pa),
    {
        self.ar[pcid].0.map(va, pa);
    }

    #[verifier(external_body)]
    pub fn pcid_unmap(&mut self, pcid:Pcid, va:VAddr) -> (ret: PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].0.wf(),
        old(self)@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va),
    ensures
        self.wf(),
        self@[pcid as int].0.wf(),
        self@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == false,
        old(self)@[pcid as int].0.tmp_get_mem_mappings()[va] == ret,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].0.tmp_get_mem_mappings() =~= old(self)@[pcid as int].0.tmp_get_mem_mappings().remove(va),
    {
        return self.ar[pcid].0.unmap(va);
    }

    #[verifier(external_body)]
    pub fn pcid_create_va_entry(&mut self, pcid:Pcid, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].0.wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self@[pcid as int].0.wf(),
            page_alloc.wf(),
            self@[pcid as int].0.tmp_page_table_page_closure() =~= old(self)@[pcid as int].0.tmp_page_table_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self@[pcid as int].0.va_entry_exists(va) == true,
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int]
    {
        return self.ar[pcid].0.create_va_entry(va, page_alloc);
    }
}
}
