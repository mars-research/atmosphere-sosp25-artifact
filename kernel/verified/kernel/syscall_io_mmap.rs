use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;

impl Kernel {
    pub fn syscall_io_mmap(&mut self, thread_ptr: ThreadPtr, va_range: VaRange4K) -> (ret:
        SyscallReturnStruct)
        requires
            old(self).total_wf(),
            old(self).thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len * 4 < usize::MAX,
    {
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let ioid_op = self.proc_man.get_proc(proc_ptr).ioid;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;

        proof {
            self.proc_man.thread_inv();
            self.proc_man.process_inv();
        }

        if ioid_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let ioid = ioid_op.unwrap();

        if self.proc_man.get_container(container_ptr).quota.mem_4k < va_range.len * 4 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::ErrorNoQuota);
        }
        assert(self.page_alloc.free_pages_4k.len() >= va_range.len * 4) by {
            old(self).fold_mem_4k_lemma();
        }

        if self.check_io_space_va_range_free(proc_ptr, &va_range) == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::ErrorVaInUse);
        }
        let (num_page, seq_pages) = self.range_alloc_and_map_io(proc_ptr, &va_range);

        // assert(self.container_dom().fold(
        //     0,
        //     |e: int, a: ContainerPtr| e + self.get_container(a).quota.mem_4k,
        // ) == old(self).container_dom().fold(
        //     0,
        //     |e: int, a: ContainerPtr| e + old(self).get_container(a).quota.mem_4k,
        // ) - num_page) by {
        //     self.fold_change_mem_4k_lemma(*old(self), container_ptr);
        // }
        // assert(self.total_wf());

        // assert(forall|j: usize|
        //     #![auto]
        //     0 <= j < seq_pages@.len() ==> old(self).page_alloc.mapped_pages_4k().contains(
        //         seq_pages@[j as int],
        //     ) == false);
        // assert(forall|page_ptr: PagePtr|
        //     #![auto]
        //     seq_pages@.contains(page_ptr) ==> old(self).get_physical_page_mapping().dom().contains(
        //         page_ptr,
        //     ) == false);

        // assert(forall|i: usize|
        //     #![auto]
        //     0 <= i < va_range.len ==> old(self).page_alloc.page_is_mapped(
        //         self.get_address_space(proc_ptr)[va_range@[i as int]].addr,
        //     ) == false);

        // assert(forall|p_ptr: ProcPtr, va: VAddr|
        //     #![auto]
        //     old(self).proc_dom().contains(p_ptr) && old(self).get_address_space(
        //         p_ptr,
        //     ).dom().contains(va) ==> old(self).page_alloc.page_is_mapped(
        //         old(self).get_address_space(p_ptr)[va].addr,
        //     ) == true);

        // assert(forall|i: usize, p_ptr: ProcPtr, va: VAddr|
        //     #![auto]
        //     0 <= i < va_range.len && old(self).proc_dom().contains(p_ptr) && old(
        //         self,
        //     ).get_address_space(p_ptr).dom().contains(va) ==> self.get_address_space(
        //         proc_ptr,
        //     )[va_range@[i as int]].addr != old(self).get_address_space(p_ptr)[va].addr);

        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessSeqUsize { value: seq_pages });
    }
}

} // verus!
