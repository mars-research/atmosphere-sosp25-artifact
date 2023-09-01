use core::marker::PhantomData;

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

/// An arena of the size of a page.
///
/// It splits a page into multiple Elements.
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub tracked struct PageArena<T> {
    phantom: PhantomData<T>,
    no_copy: NoCopy,
}

pub ghost struct PageArenaData<T> {
    pub pptr: PagePPtr,
    pub perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>,
    pub values: Seq<Option<T>>,
}

/// A pointer to an element in a page arena.
pub struct PageElementPtr<T> {
    page_pptr: PagePPtr,
    index: usize,

    phantom: Ghost<Option<T>>,
}

impl<T> PageArena<T> {
    pub spec fn view(self) -> PageArenaData<T>;

    pub fn from_page(
        pptr: PagePPtr,
        perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            pa.is_Some() ==> (
                pa.get_Some_0()@.wf()
                && pa.get_Some_0()@@.pptr.id() == pptr.id()
            ),
    {
        // This will be optimized out
        if Self::capacity_opt().is_none() {
            return None;
        }
        assert(Self::fits_one_page());

        Some(Self::wrap_perm(pptr, perm))
    }

    /// Returns the PageElementPtr associated with an index.
    ///
    /// Since PageArena is entirely ghost, the real page PPtr
    /// needs to be specified.
    pub fn get_element_ptr(arena: &Tracked<Self>, page_pptr: PagePPtr, i: usize) -> (ep: PageElementPtr<T>)
        requires
            0 <= i < Self::spec_capacity(),
            page_pptr.id() == arena@@.pptr.id(),
            arena@.wf(),
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

    // Specs

    pub open spec fn wf(&self) -> bool {
        Self::fits_one_page()
    }

    pub open spec fn fits_one_page() -> bool {
        Self::spec_capacity_opt().is_Some()
    }

    pub open spec fn spec_capacity() -> usize;

    pub spec fn spec_capacity_opt() -> Option<usize>;

    pub open spec fn has_element(&self, element: &PageElementPtr<T>) -> bool {
        self@.pptr.id() == element.page_base() && element.index() < Self::spec_capacity()
    }

    pub open spec fn values(&self) -> &Seq<Option<T>> {
        &self@.values
    }

    pub open spec fn value_at(&self, index: nat) -> &Option<T> {
        &self@.values[index as int]
    }

    // TODO: Strengthen
    pub open spec fn same_arena(&self, arena: Self) -> bool {
        self@.pptr.id() == arena@.pptr.id()
    }

    // Trusted methods

    #[verifier(external_body)]
    fn wrap_perm(
        pptr: PagePPtr,
        perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>,
    ) -> (pa: Tracked<Self>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            pa@@.init(pptr, perm)
    {
        Tracked::assume_new()
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_capacity_opt))]
    pub const fn capacity_opt() -> (ret: Option<usize>)
        ensures
            ret == Self::spec_capacity_opt(),
            ret.is_Some() ==> (
                Self::fits_one_page()
                && Self::spec_capacity() == ret.get_Some_0()
            ),
    {
        let type_size = core::mem::size_of::<T>();
        if type_size == 0 || type_size > PAGE_SIZE {
            None
        } else {
            Some(PAGE_SIZE / type_size)
        }
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity() -> (ret: usize)
        requires
            Self::fits_one_page(),
        ensures
            Self::spec_capacity() == ret,
    {
        PAGE_SIZE / core::mem::size_of::<T>()
    }
}

impl<T> PageArenaData<T> {
    spec fn init(&self, pptr: PagePPtr, perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>) -> bool {
        self.perm === perm
        && self.pptr === pptr
        && self.is_empty()
    }

    spec fn is_empty(&self) -> bool {
        forall |i: int| i <= PageArena::<T>::capacity() ==> #[trigger] self.values[i].is_None()
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

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr.id()
    }

    pub closed spec fn index(&self) -> nat {
        self.index as nat
    }

    pub closed spec fn in_arena(&self, arena: &Tracked<PageArena<T>>) -> bool {
        arena@@.pptr.id() == self.page_base()
    }

    // Trusted methods

    #[verifier(external_body)]
    #[inline(always)]
    pub fn borrow(&self, arena: &Tracked<PageArena<T>>) -> (result: &T)
        requires
            arena@.wf(),
            arena@.has_element(self),
            arena@.value_at(self.index()).is_Some(),
        ensures
            result == arena@.value_at(self.index()).get_Some_0(),
    {
        unsafe {
            let slice = core::slice::from_raw_parts(self.page_pptr.to_usize() as *const T, PageArena::<T>::capacity());
            &slice[self.index]
        }
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn put(&self, arena: &mut Tracked<PageArena<T>>, value: T)
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
                i < PageArena::<T>::capacity() && i != self.index() ==>
                    #[trigger] old(arena)@.value_at(i) == arena@.value_at(i),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(self.page_pptr.to_usize() as *mut T, PageArena::<T>::capacity());
            slice[self.index] = value;
        }
    }

    /*
    // Fn arguments with reference arguments require this patch:
    //
    // https://github.com/verus-lang/verus/pull/761
    // https://github.com/verus-lang/verus/issues/576
    #[verifier(external_body)]
    pub fn do_mut<const N: usize>(
        &self,
        arena: &mut Tracked<PageArena<T, N>>,
        f: impl FnOnce(&mut T),
    )
        requires
            old(arena)@.has_element(self),
        ensures
            arena@.same_arena(old(arena)@),
            arena@.has_element(self),
            // no way to refer to new value of &mut T from closure :/
    {
        todo!()
    }
    */
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
    struct SomeElement(u64);

    fn test_element_ptr(pptr: PagePPtr) {
        // assumptions
        if size_of::<SomeElement>() != 8 { return; }
        if usize::MAX - pptr.to_usize() < 4096 { return; }

        let first: PageElementPtr<SomeElement> = PageElementPtr {
            page_pptr: pptr,
            index: 0,

            phantom: Ghost(None),
        };
    }

    fn test_boot_page(page1: BootPage, page2: BootPage) {
        let (pptr1, perm1) = PPtr::from_boot_page(page1);
        let (pptr2, perm2) = PPtr::from_boot_page(page2);

        let mut arena1 = if let Some(arena) = PageArena::<usize>::from_page(pptr1.clone(), perm1) {
            arena
        } else {
            return;
        };
        let arena2 = if let Some(arena) = PageArena::<usize>::from_page(pptr2.clone(), perm2) {
            arena
        } else {
            return;
        };

        if PageArena::<usize>::capacity() < 5 {
            return;
        }

        let p1 = PageArena::get_element_ptr(&arena1, pptr1.clone(), 0);
        let p2 = PageArena::get_element_ptr(&arena1, pptr1.clone(), 1);

        let p3 = PageArena::get_element_ptr(&arena2, pptr2.clone(), 0);
        let p4 = PageArena::get_element_ptr(&arena2, pptr2.clone(), 1);
        //let bad = PageArena::get_element_ptr(&arena2, pptr1.clone(), 3);

        p1.put(&mut arena1, 123);
        p2.put(&mut arena1, 233);
        let p2_clone = p2.clone();

        let v1 = p1.borrow(&arena1);
        let v2 = p2.borrow(&arena1);
        assert(v1 == 123);
        assert(v2 == 233);

        p2_clone.put(&mut arena1, 666);
        let v2 = p2.borrow(&arena1);
        assert(v2 == 666);
    }
}

}
