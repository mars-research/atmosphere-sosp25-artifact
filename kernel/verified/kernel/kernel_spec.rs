use vstd::prelude::*;
verus!{

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::*;
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;
use vstd::ptr::*;
use crate::trap::PtRegs;
use crate::iommutable::*;

// use core::mem::MaybeUninit;

#[cfg(verus_keep_ghost)]
use vstd::set_lib::lemma_set_properties;

pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub mmu_man: MMUManager,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
    pub cpu_stacks: CPUStackList,

    pub kernel_pml4_entry: usize,
}

impl Kernel{
    #[verifier(external_body)]
    pub fn new() -> (ret: Kernel)
        ensures
            ret.proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            ret.proc_man.proc_perms@ =~= Map::empty(),
            ret.proc_man.thread_ptrs@ =~= Set::empty(),
            ret.proc_man.thread_perms@ =~= Map::empty(),
            ret.proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            ret.proc_man.scheduler@ =~= Seq::empty(),
            ret.proc_man.endpoint_ptrs@ =~= Set::empty(),
            ret.proc_man.endpoint_perms@ =~= Map::empty(),
            ret.proc_man.pcid_closure@ =~= Set::empty(),
            ret.proc_man.ioid_closure@ =~= Set::empty(),

            ret.page_alloc.page_array.wf(),
            ret.page_alloc.free_pages.wf(),
            ret.page_alloc.free_pages.len() == 0,
            ret.page_alloc.page_table_pages@ =~= Set::empty(),
            ret.page_alloc.allocated_pages@ =~= Set::empty(),
            ret.page_alloc.mapped_pages@ =~= Set::empty(),
            ret.page_alloc.available_pages@ =~= Set::empty(),
            ret.page_alloc.page_perms@.dom() =~= Set::empty(),

            ret.mmu_man.free_pcids.wf(),
            ret.mmu_man.free_pcids@ =~= Seq::empty(),
            ret.mmu_man.page_tables.wf(),
            ret.mmu_man.page_table_pages@ =~= Set::empty(),
            ret.mmu_man.iommu_ids@ =~= Set::empty(),
            ret.mmu_man.iommu_perms@ =~= Map::empty(),
            ret.mmu_man.iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  ret.mmu_man.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l1_tables@ =~= Map::empty(),

            ret.cpu_list.wf(),
    {
        let ret = Self {
            proc_man : ProcessManager::new(),
            page_alloc : PageAllocator::new(),
            mmu_man: MMUManager::new(),
            cpu_list: MarsArray::<Cpu,NUM_CPUS>::new(),
            cpu_stacks: CPUStackList::new(),
            kernel_pml4_entry: 0,
        };
        ret
    }


    // #[verifier(external_body)]
    pub fn kernel_init(&mut self, boot_page_ptrs: &ArrayVec<(PageState,VAddr),NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>, 
                        dom0_pagetable: PageTable, dom0_iommu_cr3:usize,dom0_iommutable: PointsTo<IOMMUTable>, kernel_pml4_entry: usize, dom0_pt_regs: PtRegs) -> (ret: isize)
        requires
            old(self).proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            old(self).proc_man.proc_perms@ =~= Map::empty(),
            old(self).proc_man.thread_ptrs@ =~= Set::empty(),
            old(self).proc_man.thread_perms@ =~= Map::empty(),
            old(self).proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            old(self).proc_man.scheduler@ =~= Seq::empty(),
            old(self).proc_man.endpoint_ptrs@ =~= Set::empty(),
            old(self).proc_man.endpoint_perms@ =~= Map::empty(),
            old(self).proc_man.pcid_closure@ =~= Set::empty(),
            old(self).proc_man.ioid_closure@ =~= Set::empty(),
            
            old(self).page_alloc.page_array.wf(),
            old(self).page_alloc.free_pages.wf(),
            old(self).page_alloc.free_pages.len() == 0,
            old(self).page_alloc.page_table_pages@ =~= Set::empty(),
            old(self).page_alloc.allocated_pages@ =~= Set::empty(),
            old(self).page_alloc.mapped_pages@ =~= Set::empty(),
            old(self).page_alloc.available_pages@ =~= Set::empty(),
            old(self).page_alloc.page_perms@.dom() =~= Set::empty(),
            
            old(self).mmu_man.free_pcids.wf(),
            old(self).mmu_man.free_pcids@ =~= Seq::empty(),
            old(self).mmu_man.page_tables.wf(),
            old(self).mmu_man.page_table_pages@ =~= Set::empty(),
            old(self).mmu_man.iommu_ids@ =~= Set::empty(),
            old(self).mmu_man.iommu_perms@ =~= Map::empty(),
            old(self).mmu_man.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  old(self).mmu_man.get_pagetable_mapping_by_pcid(i)[va].is_None(),

            old(self).cpu_list.wf(),

            boot_page_ptrs.wf(),
            boot_page_ptrs.len() == NUM_PAGES,
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].1 == page_index2page_ptr(i)),
            (forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].1 == page_ptr),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 <= IO),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 != ALLOCATED),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && (boot_page_ptrs@[i as int].0 == FREE || boot_page_ptrs@[i as int].0 == MAPPED || boot_page_ptrs@[i as int].0 == IO)==> 
                (boot_page_perms@.dom().contains(page_index2page_ptr(i))
                 && 
                 boot_page_perms@[page_index2page_ptr(i)]@.pptr == page_index2page_ptr(i)
                 &&
                 boot_page_perms@[page_index2page_ptr(i)]@.value.is_Some()
                )
            ),
            NUM_PAGES * 4096 <= usize::MAX,

            dom0_pagetable.wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                page_ptr_valid(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                va_perm_bits_valid(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().perm),
            dom0_iommutable@.pptr == dom0_iommu_cr3,
            dom0_iommutable@.value.is_Some(),
            dom0_iommutable@.value.get_Some_0().wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                page_ptr_valid(dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                va_perm_bits_valid(dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().perm),
            dom0_pagetable.get_pagetable_page_closure().disjoint(dom0_iommutable@.value.get_Some_0().get_iommutable_page_closure()),
            
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].0 == MAPPED 
                ||
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].0 == IO,
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                boot_page_ptrs[page_ptr2page_index(dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().addr) as int].0 == IO,
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].1 == va,
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                boot_page_ptrs[page_ptr2page_index(dom0_iommutable@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().addr) as int].1 == va,
            forall|page_ptr:PagePtr|#![auto] (dom0_pagetable.get_pagetable_page_closure() + dom0_iommutable@.value.get_Some_0().get_iommutable_page_closure()).contains(page_ptr)
                 <==>
                 (
                    page_ptr_valid(page_ptr)
                    &&
                    0<=page_ptr2page_index(page_ptr as usize)<NUM_PAGES
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
                 ) 
    {
        proof{page_ptr_lemma();}
        self.cpu_list.init_to_none();
        self.proc_man.proc_man_init();
        self.mmu_man.mmu_man_init();
        assert(self.proc_man.wf());
        assert(self.mmu_man.wf());
        self.page_alloc.init(boot_page_ptrs,boot_page_perms, dom0_iommu_cr3);
        assert(self.page_alloc.wf());
        self.mmu_man.adopt_dom0(dom0_pagetable,dom0_iommu_cr3,dom0_iommutable);
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.mmu_man.get_iommu_ids() =~= Set::empty().insert(dom0_iommu_cr3));
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mem_layout_wf());
        if self.page_alloc.free_pages.len() < 2{
            return -1;
        }
        else{
            let (page_ptr1, page_perm1) = self.page_alloc.alloc_kernel_mem(); 
            let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem();
            let new_proc = self.proc_man.new_proc(page_ptr1, page_perm1, 0, Some(dom0_iommu_cr3));
            let new_thread = self.proc_man.new_thread(dom0_pt_regs,page_ptr2, page_perm2,new_proc);
            assert(
                self.proc_man.wf());
            assert(
                self.mmu_man.wf()
            );
            assert(
                self.page_alloc.wf()
            );
            assert(
                self.cpu_list.wf()
            );
            assert(
                self.kernel_cpu_list_wf()
            );
            assert(
                self.kernel_mem_layout_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_pagetable_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_iommutable_wf()
            );
            assert(self.kernel_proc_mmu_wf());
            assert(self.kernel_proc_no_thread_in_transit());
            assert(self.kernel_tlb_wf());
            return 0;
        }


    }
    pub open spec fn kernel_mmu_page_alloc_pagetable_wf(&self) -> bool{
        &&&
        (
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).contains((pcid,va))
            )
        )
    }

    pub open spec fn kernel_mmu_page_alloc_iommutable_wf(&self) -> bool{
        &&&
        (
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).contains((ioid,va))
            )
        )
    }

    pub open spec fn kernel_proc_mmu_wf(&self) -> bool{
        &&&
        (forall|pcid:Pcid|#![auto] self.proc_man.get_pcid_closure().contains(pcid) ==> 
            (0 <= pcid< PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false))
        &&&
        (self.proc_man.get_ioid_closure() =~= self.mmu_man.get_iommu_ids())
    }

    pub open spec fn kernel_proc_no_thread_in_transit(&self) -> bool{
        &&&
        (forall|thread_ptr:ThreadPtr|#![auto] self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> 
            self.proc_man.get_thread(thread_ptr).state != TRANSIT)
    }

    pub open spec fn kernel_mem_layout_wf(&self) -> bool {
        // all pages used to construct pagetable/iommutables are marked correctly in page allocator 
        &&&
        (self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure())
        &&&
        (self.page_alloc.get_allocated_pages() =~= self.proc_man.get_proc_man_page_closure())
    }

    pub open spec fn kernel_cpu_list_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS 
                ==> (
                    self.cpu_list[cpu_id as int].wf()
                    )
        )
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS && self.cpu_list[cpu_id as int].get_is_idle() == false
                ==> (
                    self.proc_man.get_thread_ptrs().contains(self.cpu_list[cpu_id as int].get_current_thread().unwrap())
                    &&
                    self.proc_man.get_thread(self.cpu_list[cpu_id as int].get_current_thread().unwrap()).state == RUNNING
                    )
        )
    }
    pub open spec fn kernel_tlb_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) 
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid) =~= Map::empty()
                )
        )
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None()
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false

                )
        )        
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some()
                ==> (
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false)
                    ||
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid)[va] =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0())
                )
        )
    }

    pub open spec fn wf(&self) -> bool{        
        &&&
        (
            self.proc_man.wf()
        )
        &&&
        (
            self.mmu_man.wf()
        )
        &&&
        (
            self.page_alloc.wf()
        )
        &&&
        (
            self.cpu_list.wf()
        )
        &&&
        (
            self.kernel_cpu_list_wf()
        )
        &&&
        (
            self.kernel_mem_layout_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_pagetable_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_iommutable_wf()
        )
        &&&
        (self.kernel_proc_mmu_wf())
        &&&
        (self.kernel_proc_no_thread_in_transit())
        &&&
        (self.kernel_tlb_wf())
    }

    pub proof fn pagetable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_mmu_page_alloc_pagetable_wf(),
        ensures
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()),
    {
        lemma_set_properties::<Set<PagePtr>>();  
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).len() > 0
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).state == MAPPED
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr)
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                exists|va:usize| #![auto] spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr =~= pa
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                self.page_alloc.get_mapped_pages().contains(pa)
            )
        );
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()));
    }

    
    pub proof fn iommutable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_mmu_page_alloc_iommutable_wf(),
        ensures
            forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).subset_of(self.page_alloc.get_mapped_pages()),
            forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_page_table_pages()),
            forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_free_pages_as_set()),
            forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_allocated_pages()),
    {
        lemma_set_properties::<Set<PagePtr>>();  
        assert(
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).len() > 0
            )
        );
        assert(
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_page(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).state == MAPPED
            )
        );
        assert(
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr)
            )
        );
        assert(
            forall|ioid:IOid, pa:PAddr| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && page_ptr_valid(pa) && self.mmu_man.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages().contains(pa) ==>
            (
                exists|va:usize| #![auto] spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr =~= pa
            )
        );
        assert(
            forall|ioid:IOid, pa:PAddr| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && page_ptr_valid(pa) && self.mmu_man.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages().contains(pa) ==>
            (
                self.page_alloc.get_mapped_pages().contains(pa)
            )
        );
        assert(forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).subset_of(self.page_alloc.get_mapped_pages()));
        assert(forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_page_table_pages()));
        assert(forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_free_pages_as_set()));
        assert(forall|ioid:IOid| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_allocated_pages()));
    }

}

}
