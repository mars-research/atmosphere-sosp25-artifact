use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SIZE,
};

use crate::mem::size_of;

verus! {

// Why 4096 instead of PAGE_SIZE in some places?
//
// https://github.com/verus-lang/verus/issues/587

pub type PagePPtr = PPtr<[u8; PAGE_SIZE]>;
pub type PagePerm = PointsTo<[u8; PAGE_SIZE]>;

/// An arena of the size of a page.
///
/// It splits a page into an array of `T`s followed by an optional
/// per-page metadata value.
///
/// Sadly, Verus cannot handle generics with a default type yet, so
/// do `PageArena<T, ()>` if you don't use the metadata.
///
/// Alternatively, for ergonomics we could rename the struct to
/// `PageArenaWithMeta<T, MT>` and have `PageArena<T>` be the type
/// alias.
pub tracked struct PageArena<T, MT> {
    pptr: PagePPtr,

    perm: Tracked<PagePerm>,
    values: Seq<Option<T>>,
    metadata: MT,
}

/// A pointer to an element in a page arena.
pub struct PageElementPtr<T> {
    page_pptr: PagePPtr,
    index: usize,

    // PhantomData makes the type opaque
    phantom: Ghost<Option<T>>,
}

// A pointer to the per-page metadata in a page arena.
pub struct PageMetadataPtr<MT> {
    page_pptr: PagePPtr,

    // PhantomData makes the type opaque
    phantom: Ghost<Option<MT>>,
}

impl<T> PageArena<T, ()> {
    /// Creates an arena without metadata.
    pub fn from_page(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            pa.is_Some() ==> (
                pa.get_Some_0()@.wf()
                && pa.get_Some_0()@.page_base() == pptr.id()
            ),
    {
        // This will be optimized out
        if Self::capacity_opt().is_none() {
            return None;
        }

        Some(Self::init_ghost(pptr, perm, ()))
    }
}

impl<T, MT> PageArena<T, MT> {
    /// Creates an arena with metadata.
    pub fn from_page_with_metadata(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
        metadata: MT,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            pa.is_Some() ==> (
                pa.get_Some_0()@.wf()
                && pa.get_Some_0()@.page_base() == pptr.id()
                && pa.get_Some_0()@.metadata() == metadata
            ),
    {
        // This will be optimized out
        if Self::capacity_opt().is_none() {
            return None;
        }

        Some(Self::init_ghost(pptr, perm, metadata))
    }

    /// Returns the PageElementPtr associated with an index.
    ///
    /// Since PageArena is entirely ghost, the real page PPtr
    /// needs to be specified.
    pub fn get_element_ptr(arena: &Tracked<Self>, page_pptr: PagePPtr, i: usize) -> (ep: PageElementPtr<T>)
        requires
            arena@.wf(),
            0 <= i < Self::capacity(),
            page_pptr.id() == arena@.page_base(),
        ensures
            ep.index() == i,
            arena@.has_element(&ep),
    {
        PageElementPtr {
            page_pptr,
            index: i,

            phantom: Ghost(None),
        }
    }

    /// Returns the PageMetadataPtr associated with this page.
    pub fn get_metadata_ptr(arena: &Tracked<Self>, page_pptr: PagePPtr) -> (mp: PageMetadataPtr<MT>)
        requires
            arena@.wf(),
    {
        PageMetadataPtr {
            page_pptr,

            phantom: Ghost(None),
        }
    }

    const fn capacity_opt() -> (ret: Option<usize>)
        ensures
            ret.is_Some() ==> (
                Self::type_is_storable()
                && Self::spec_capacity() == ret.get_Some_0()
            ),
    {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();

        if metadata_size > 4096 {
            // In reality, metadata_size == PAGE_SIZE is also unacceptable
            // and will fail the following check
            return None;
        }

        let remaining_size = 4096 - metadata_size;
        if type_size == 0 || type_size > remaining_size {
            None
        } else {
            Some(remaining_size / type_size)
        }
    }

    // Specs

    pub open spec fn wf(&self) -> bool {
        Self::type_is_storable()
    }

    pub open spec fn type_is_storable() -> bool {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size: usize = (4096usize - metadata_size) as usize;

        &&& metadata_size <= 4096
        &&& 0 < type_size <= remaining_size
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity() -> (ret: usize)
        requires
            Self::type_is_storable(),
        ensures
            ret == Self::spec_capacity(),
    {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size = 4096usize - metadata_size;

        remaining_size / size_of::<T>()
    }

    pub open spec fn spec_capacity() -> usize {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size: usize = (4096usize - metadata_size) as usize;

        remaining_size / size_of::<T>()
    }

    #[verifier(when_used_as_spec(spec_metadata_offset))]
    pub const fn metadata_offset() -> (ret: usize)
        by (nonlinear_arith)
        requires
            Self::type_is_storable(),
        ensures
            ret == Self::spec_metadata_offset(),
            ret + size_of::<MT>() <= 4096,
    {
        let type_size = size_of::<T>();
        let capacity = Self::capacity();

        type_size * capacity
    }

    pub open spec fn spec_metadata_offset() -> usize {
        let type_size = size_of::<T>();
        let capacity = Self::capacity();

        (type_size * capacity) as usize
    }

    pub open spec fn has_element(&self, element: &PageElementPtr<T>) -> bool {
        self.page_base() == element.page_base() && element.index() < Self::capacity()
    }

    pub open spec fn same_arena(&self, arena: Self) -> bool {
        // Type system ensures identical element types and therefore capacity
        self.page_base() == arena.page_base()
    }

    pub closed spec fn value_at(&self, index: nat) -> &Option<T> {
        &self.values[index as int]
    }

    pub closed spec fn metadata(&self) -> &MT {
        &self.metadata
    }

    pub closed spec fn page_base(&self) -> int {
        self.pptr.id()
    }

    spec fn is_empty(&self) -> bool {
        forall |i: int| i <= PageArena::<T, MT>::capacity() ==> #[trigger] self.values[i].is_None()
    }

    // Trusted methods

    #[verifier(external_body)]
    fn init_ghost(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
        metadata: MT,
    ) -> (ret: Tracked<Self>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            ret@.perm === perm,
            ret@.pptr === pptr,
            ret@.page_base() === pptr.id(),
            ret@.metadata === metadata,
            ret@.is_empty(),
    {
        Tracked::assume_new()
    }
}


impl<T> PageElementPtr<T> {
    pub fn clone(&self) -> (ep: Self)
        ensures
            self.same_ptr(&ep),
    {
        Self {
            page_pptr: self.page_pptr.clone(),
            index: self.index,

            phantom: self.phantom,
        }
    }

    // Specs

    pub closed spec fn same_ptr(&self, other: &Self) -> bool {
        self.page_pptr.id() === other.page_pptr.id() && self.index == other.index
    }

    pub closed spec fn page_pptr(&self) -> PagePPtr {
        self.page_pptr
    }

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr.id()
    }

    pub closed spec fn index(&self) -> nat {
        self.index as nat
    }

    // Trusted methods

    #[verifier(external_body)]
    #[inline(always)]
    pub fn borrow<MT>(&self, arena: &Tracked<PageArena<T, MT>>) -> (result: &T)
        requires
            arena@.wf(),
            arena@.has_element(self),
            arena@.value_at(self.index()).is_Some(),
        ensures
            result == arena@.value_at(self.index()).get_Some_0(),
    {
        unsafe {
            let slice = core::slice::from_raw_parts(self.page_pptr.to_usize() as *const T, PageArena::<T, MT>::capacity());
            &slice[self.index]
        }
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn put<MT>(&self, arena: &mut Tracked<PageArena<T, MT>>, value: T)
        requires
            old(arena)@.wf(),
            old(arena)@.has_element(self),
        ensures
            arena@.wf(),
            arena@.same_arena(old(arena)@),

            // The element was changed
            arena@.value_at(self.index()) == Some(value),

            // Everything else was unchanged
            forall |i: nat|
                i < PageArena::<T, MT>::capacity() && i != self.index() ==>
                    #[trigger] old(arena)@.value_at(i) == arena@.value_at(i),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(self.page_pptr.to_usize() as *mut T, PageArena::<T, MT>::capacity());
            slice[self.index] = value;
        }
    }
}

impl<MT> PageMetadataPtr<MT> {
    pub fn clone(&self) -> (ep: Self)
        ensures
            self.same_ptr(&ep),
    {
        Self {
            page_pptr: self.page_pptr.clone(),

            phantom: self.phantom,
        }
    }

    // Specs

    pub closed spec fn same_ptr(&self, other: &Self) -> bool {
        self.page_pptr.id() === other.page_pptr.id()
    }

    pub closed spec fn page_pptr(&self) -> PagePPtr {
        self.page_pptr
    }

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr.id()
    }

    // Trusted methods

    #[verifier(external_body)]
    #[inline(always)]
    pub fn borrow<T>(&self, arena: &Tracked<PageArena<T, MT>>) -> (result: &MT)
        requires
            arena@.wf(),
        ensures
            result == arena@.metadata(),
    {
        // FIXME: Might overflow?
        let ptr = self.page_pptr.to_usize() + PageArena::<T, MT>::metadata_offset();
        unsafe {
            &*(ptr as *const MT)
        }
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn put<T>(&self, arena: &mut Tracked<PageArena<T, MT>>, value: MT)
        requires
            old(arena)@.wf(),
        ensures
            arena@.same_arena(old(arena)@),

            // The metadata was changed
            arena@.metadata() == value,

            // Everything else was unchanged
            forall |i: nat|
                i < PageArena::<T, MT>::capacity() ==>
                    #[trigger] old(arena)@.value_at(i) == arena@.value_at(i),
    {
        // FIXME: Might overflow?
        let ptr = self.page_pptr.to_usize() + PageArena::<T, MT>::metadata_offset();
        unsafe {
            *(ptr as *mut MT) = value;
        }
    }
}

#[verifier::external_fn_specification]
pub fn ex_usize_checked_mul(lhs: usize, rhs: usize) -> (result: Option<usize>)
    ensures
        lhs * rhs > usize::MAX ==> result.is_None(),
        lhs * rhs <= usize::MAX ==> (
            result == Some((lhs * rhs) as usize) // usize
            && (lhs as usize) * (rhs as usize) <= usize::MAX
            && result.get_Some_0() == lhs * rhs  // nat
        ),
{
    lhs.checked_mul(rhs)
}

mod test {
    use super::*;

    use vstd::ptr::BootPage;

    #[repr(transparent)]
    struct SomeStruct(u64);

    /// A simple arena of usize without metadata.
    type UsizeArena = PageArena<usize, ()>;

    /// An arena with per-page metadata.
    type MetaArena = PageArena<usize, SomeStruct>;

    fn test_element_ptr(pptr: PagePPtr) {
        // assumptions
        if usize::MAX - pptr.to_usize() < 4096 { return; }

        let first: PageElementPtr<SomeStruct> = PageElementPtr {
            page_pptr: pptr,
            index: 0,

            phantom: Ghost(None),
        };
    }

    fn test_boot_page(page1: BootPage, page2: BootPage) {
        let (pptr1, perm1) = PPtr::from_boot_page(page1);
        let (pptr2, perm2) = PPtr::from_boot_page(page2);

        let mut arena1 = if let Some(arena) = UsizeArena::from_page(pptr1.clone(), perm1) {
            arena
        } else {
            return;
        };
        let arena2 = if let Some(arena) = UsizeArena::from_page(pptr2.clone(), perm2) {
            arena
        } else {
            return;
        };

        if UsizeArena::capacity() < 5 {
            return;
        }

        let p1 = UsizeArena::get_element_ptr(&arena1, pptr1.clone(), 0);
        let p2 = UsizeArena::get_element_ptr(&arena1, pptr1.clone(), 1);

        let p3 = UsizeArena::get_element_ptr(&arena2, pptr2.clone(), 0);
        let p4 = UsizeArena::get_element_ptr(&arena2, pptr2.clone(), 1);
        //let bad = UsizeArena::get_element_ptr(&arena2, pptr1.clone(), 3);

        p1.put(&mut arena1, 123);
        p2.put(&mut arena1, 233);
        assert(arena1@.wf());
        let p2_clone = p2.clone();

        let v1 = p1.borrow(&arena1);
        let v2 = p2.borrow(&arena1);
        assert(v1 == 123);
        assert(v2 == 233);

        p2_clone.put(&mut arena1, 666);
        let v2 = p2.borrow(&arena1);
        assert(v2 == 666);
    }

    fn test_metadata(page: BootPage) {
        let (pptr, perm) = PPtr::from_boot_page(page);

        let mut arena = if let Some(arena) = MetaArena::from_page_with_metadata(pptr.clone(), perm, SomeStruct(123)) {
            arena
        } else {
            return;
        };

        let mp = MetaArena::get_metadata_ptr(&arena, pptr.clone());
        let mp_clone = MetaArena::get_metadata_ptr(&arena, pptr);
        let meta = mp.borrow(&arena);
        assert(meta.0 == 123);

        mp_clone.put(&mut arena, SomeStruct(233));
        let meta = mp.borrow(&arena);
        assert(meta.0 == 233);
    }
}

}
