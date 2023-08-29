use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::ptr::{
    PPtr, PointsTo,
    PAGE_SIZE,
};

use super::mem::{size_of, spec_size_of};

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
pub tracked struct PageArena<T, const N: usize> {
    phantom: PhantomData<T>,
    no_copy: NoCopy,
}

pub ghost struct PageArenaData<T, const N: usize> {
    pub pptr: PagePPtr,
    pub perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>,
    pub values: [Option<T>; N],
}

/// A pointer to an element in a page arena.
pub struct PageElementPtr<T> {
    ptr: usize,

    page_pptr: Ghost<PagePPtr>,
    index: Ghost<nat>,
    phantom: Ghost<Option<T>>,
}

impl<T, const N: usize> PageArena<T, N> {
    pub spec fn view(self) -> PageArenaData<T, N>;

    pub fn from_page(
        pptr: PagePPtr,
        perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            N > 0,
            pptr.id() === perm@@.pptr
        ensures
            pa.is_Some() ==> (
                Self::fits_one_page()
                && pa.get_Some_0()@.wf()
                && pa.get_Some_0()@@.pptr.id() == pptr.id()
            ),
    {
        // This will be optimized out
        if !Self::fits_one_page() {
            return None;
        }
        assert(Self::spec_fits_one_page());

        // Lightweight runtime check
        //
        // TODO: Can probably be guaranteed on the BootPage side
        if usize::MAX - pptr.to_usize() < 4096 {
            return None;
        }
        assert(pptr.id() + PAGE_SIZE <= usize::MAX);

        Some(Self::wrap_perm(pptr, perm))
    }

    /// Returns the PageElementPtr associated with an index.
    ///
    /// Since PageArena is entirely ghost, the real page PPtr
    /// needs to be specified.
    pub fn get_element_ptr(arena: &Tracked<Self>, page_pptr: PagePPtr, i: usize) -> (ep: PageElementPtr<T>)
        requires
            0 <= i < N,
            page_pptr.id() == arena@@.pptr.id(),
            arena@.wf(),
        ensures
            ep.wf(),
            ep.index() == i,
            arena@.has_element(&ep),

            ep.ptr() == Self::spec_ptr_at(arena, page_pptr, i),
    {
        let ep: PageElementPtr<T> = PageElementPtr {
            ptr: Self::ptr_at(arena, page_pptr, i),

            page_pptr: Ghost(page_pptr),
            index: Ghost(i as nat),
            phantom: Ghost(None),
        };

        assert(ep.wf_index());
        assert(ep.wf_bounds()) by {
            // Required to prove the second clause ("Ends within the page"):
            //
            //     ep.page_offset() + spec_size_of::<T>() <= PAGE_SIZE
            //
            Self::lemma_increasing_offset((i + 1) as nat, N as nat);
            Self::lemma_offset_successor(i as nat);
        };

        assert(ep.wf());

        ep
    }

    pub const fn capacity() -> usize {
        N
    }

    // Specs

    pub open spec fn wf(&self) -> bool {
        self.wf_can_address_at_least_a_page() && Self::fits_one_page()
    }

    pub open spec fn wf_can_address_at_least_a_page(&self) -> bool {
        // Can address at least a page
        self@.pptr.id() + PAGE_SIZE <= usize::MAX
    }

    #[verifier(when_used_as_spec(spec_fits_one_page))]
    pub const fn fits_one_page() -> (fits: bool)
        requires
            N > 0
        ensures
            fits == Self::spec_fits_one_page(),
            fits ==> (
                // Every possible offset fits into the page
                forall |i: nat|
                    i < N ==>
                        #[trigger]((i * spec_size_of::<T>()) as nat) < PAGE_SIZE
            ),
    {
        // This will be optimized out
        if size_of::<T>() == 0 || size_of::<T>() > 4096 {
            return false;
        }

        if let Some(size) = N.checked_mul(size_of::<T>()) {
            let fits = size > 0 && size <= 4096;

            if fits {
                proof {
                    let total_spec_size = (N * spec_size_of::<T>()) as nat;

                    // Every possible offset fits into the page
                    assert forall |i: nat|
                        i < N ==>
                            #[trigger]((i * spec_size_of::<T>()) as nat) < total_spec_size
                    by {
                        if 0 < i < N {
                            Self::lemma_increasing_offset(i, N as nat);
                        }
                    };
                }
            }

            fits
        } else {
            false
        }
    }

    pub closed spec fn spec_fits_one_page() -> bool {
        0 < spec_size_of::<T>() <= PAGE_SIZE
        && 0 < (N * spec_size_of::<T>()) as nat <= PAGE_SIZE
    }

    pub open spec fn has_element(&self, element: &PageElementPtr<T>) -> bool
        recommends
            element.wf()
    {
        element.wf() && self@.pptr.id() == element.page_base()
    }

    pub open spec fn values(&self) -> &[Option<T>; N] {
        &self@.values
    }

    pub open spec fn value_at(&self, index: nat) -> &Option<T> {
        &self@.values[index as int]
    }

    // TODO: Strengthen
    pub open spec fn same_arena(&self, arena: Self) -> bool {
        self@.pptr.id() == arena@.pptr.id()
    }

    // Lemmas

    proof fn lemma_increasing_offset(i: nat, j: nat)
        by (nonlinear_arith)
        requires
            i <= j,
            spec_size_of::<T>() > 0,
        ensures
            i * spec_size_of::<T>() <= j * spec_size_of::<T>(),
            i < j ==> i * spec_size_of::<T>() < j * spec_size_of::<T>(),
    {
    }

    proof fn lemma_offset_successor(i: nat)
        by (nonlinear_arith)
        ensures
            // Verus really needs a nudge to understand the distributive property
            (i + 1) * spec_size_of::<T>() == i * spec_size_of::<T>() + spec_size_of::<T>()
    {
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

    // FIXME: Prove absence of overflow with usize
    #[verifier(external_body)]
    pub fn ptr_at(arena: &Tracked<Self>, page_pptr: PagePPtr, i: usize) -> (ptr: usize)
        requires
            i < N,
            page_pptr.id() == arena@@.pptr.id(),
            arena@.wf(),
        ensures
            ptr == Self::spec_ptr_at(arena, page_pptr, i),
    {
        page_pptr.to_usize() + i * size_of::<T>()
    }

    pub open spec fn spec_ptr_at(arena: &Tracked<Self>, page_pptr: PagePPtr, i: usize) -> int {
        page_pptr.id() + i as nat * spec_size_of::<T>()
    }
}

impl<T, const N: usize> PageArenaData<T, N> {
    spec fn init(&self, pptr: PagePPtr, perm: Tracked<PointsTo<[u8; PAGE_SIZE]>>) -> bool {
        self.perm === perm
        && self.pptr === pptr
        && self.is_empty()
    }

    spec fn is_empty(&self) -> bool {
        forall |i: int| i <= N ==> #[trigger] self.values@[i].is_None()
    }
}

impl<T> PageElementPtr<T> {
    pub fn clone(&self) -> (ep: Self)
        requires
            self.wf(),
        ensures
            self == ep,
            ep.wf(),
    {
        Self {
            index: self.index,

            page_pptr: self.page_pptr,
            ptr: self.ptr,
            phantom: self.phantom,
        }
    }

    // Specs

    pub open spec fn wf(&self) -> bool
        recommends
            self.wf_bounds(),
            self.wf_index(),
    {
        self.wf_bounds() && self.wf_index()
    }

    pub open spec fn wf_bounds(&self) -> bool {
        // Starts within the page
        self.ptr() >= self.page_base()
        && 0 <= self.page_offset() < PAGE_SIZE

        // Ends within the page
        && self.page_offset() + spec_size_of::<T>() <= PAGE_SIZE
    }

    pub open spec fn wf_index(&self) -> bool {
        // The index corresponds to the offset
        self.page_offset() == self.index() * spec_size_of::<T>()
    }

    // Utilities

    pub closed spec fn ptr(&self) -> usize {
        self.ptr
    }

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr@.id()
    }

    pub closed spec fn page_offset(&self) -> int {
        self.ptr - self.page_base()
    }

    pub closed spec fn index(&self) -> nat {
        self.index@
    }

    pub closed spec fn in_arena<const N: usize>(&self, arena: &Tracked<PageArena<T, N>>) -> bool {
        arena@@.pptr.id() == self.page_base()
    }

    // Trusted methods

    #[verifier(external_body)]
    pub fn borrow<const N: usize>(&self, arena: &Tracked<PageArena<T, N>>) -> (result: &T)
        requires
            self.wf(),
            arena@.has_element(self),
            arena@.value_at(self.index()).is_Some(),
        ensures
            result == arena@.value_at(self.index()).get_Some_0(),
    {
        unsafe {
            &*(self.ptr as *const T)
        }
    }

    #[verifier(external_body)]
    pub fn put<const N: usize>(&self, arena: &mut Tracked<PageArena<T, N>>, value: T)
        requires
            self.wf(),
            old(arena)@.has_element(self),
        ensures
            arena@.same_arena(old(arena)@),

            // The element was changed
            arena@.value_at(self.index()) == Some(value),

            // Everything else was unchanged
            forall |i: nat|
                i < N && i != self.index() ==>
                    #[trigger] old(arena)@.value_at(i) == arena@.value_at(i),
    {
        unsafe {
            *(self.ptr as *mut T) = value;
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
            self.wf(),
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
            ptr: pptr.to_usize() + 0 * size_of::<SomeElement>(),

            page_pptr: Ghost(pptr),
            index: Ghost(0),
            phantom: Ghost(None),
        };

        assert(first.wf());
    }

    fn test_boot_page(page1: BootPage, page2: BootPage) {
        let (pptr1, perm1) = PPtr::from_boot_page(page1);
        let (pptr2, perm2) = PPtr::from_boot_page(page2);

        let mut arena1 = if let Some(arena) = PageArena::<usize, 5>::from_page(pptr1.clone(), perm1) {
            arena
        } else {
            return;
        };
        let mut arena2 = if let Some(arena) = PageArena::<usize, 5>::from_page(pptr2.clone(), perm2) {
            arena
        } else {
            return;
        };

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
