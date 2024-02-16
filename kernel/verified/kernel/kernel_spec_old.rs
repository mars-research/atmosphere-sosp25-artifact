use vstd::prelude::*;
verus!{

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::pcid_alloc::*;
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;


// #[verifier(external_body)]
// proof fn lemma_usize_u64()
//     ensures
//         forall|x:u64| (#[trigger] x as usize as u64 == x),
// {
//     unimplemented!();
// }

pub const NUM_CPUS:usize = 32;

pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub pcid_alloc: PcidAllocator,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
}

impl Kernel {

    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            ret.proc_man.proc_perms@ =~= Map::empty(),
            ret.proc_man.thread_ptrs@ =~= Set::empty(),
            ret.proc_man.thread_perms@ =~= Map::empty(),
            ret.proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            ret.proc_man.endpoint_ptrs@ =~= Set::empty(),
            ret.proc_man.endpoint_perms@ =~= Map::empty(),
            ret.proc_man.pcid_closure@ =~= Set::empty(),
            ret.page_alloc.page_array.wf(),
            ret.page_alloc.free_pages.wf(),
            ret.page_alloc.free_pages.len() == 0,
            // ret.pcid_alloc.page_table_ptrs.wf(),
            // ret.pcid_alloc.page_table_perms@ =~= Map::empty(),
            ret.cpu_list.wf(),
    {
        let ret = Self {
            proc_man : ProcessManager::new(),
            page_alloc: PageAllocator::new(),
            pcid_alloc: arbitrary(),
            cpu_list: MarsArray::<Cpu,NUM_CPUS>::new(),
        };

        ret
    }

     

    pub fn kernel_init(&mut self, boot_page_ptrs: &ArrayVec<(PageState,VAddr),NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>, dom0_address_space: &PageTable, kernel_pml4_entry: usize)
        requires 
            old(self).proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            old(self).proc_man.proc_ptrs@ =~= Seq::empty(),
            old(self).proc_man.proc_perms@ =~= Map::empty(),
            old(self).proc_man.thread_ptrs@ =~= Set::empty(),
            old(self).proc_man.thread_perms@ =~= Map::empty(),
            old(self).proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            old(self).proc_man.scheduler@ =~= Seq::empty(),
            old(self).proc_man.endpoint_ptrs@ =~= Set::empty(),
            old(self).proc_man.endpoint_perms@ =~= Map::empty(),
            old(self).proc_man.pcid_closure@ =~= Set::empty(),
            old(self).page_alloc.page_array.wf(),
            old(self).page_alloc.free_pages.wf(),
            old(self).page_alloc.free_pages.len() == 0,
            old(self).page_alloc.page_table_pages@ =~= Set::empty(),
            old(self).page_alloc.allocated_pages@ =~= Set::empty(),
            old(self).page_alloc.mapped_pages@ =~= Set::empty(),
            old(self).page_alloc.available_pages@ =~= Set::empty(),
            old(self).page_alloc.page_perms@.dom() =~= Set::empty(),
            old(self).pcid_alloc.free_page_tables.wf(),
            old(self).pcid_alloc.free_page_tables@ =~= Seq::empty(),
            old(self).pcid_alloc.page_tables.wf(),
            old(self).pcid_alloc.page_table_pages@ =~= Set::empty(),
            boot_page_ptrs.wf(),
            boot_page_ptrs.len() == NUM_PAGES,
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 <= MAPPED),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 != ALLOCATED),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && (boot_page_ptrs@[i as int].0 == FREE || boot_page_ptrs@[i as int].0 == MAPPED)==> 
                (boot_page_perms@.dom().contains(page_index2page_ptr(i))
                 && 
                 boot_page_perms@[page_index2page_ptr(i)]@.pptr == page_index2page_ptr(i)
                 &&
                 boot_page_perms@[page_index2page_ptr(i)]@.value.is_Some()
                )
            ),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 ==PAGETABLE ==> 
                (
                    dom0_address_space.get_pagetable_page_closure().contains(page_index2page_ptr(i))
                )
            ),
            NUM_PAGES * 4096 <= usize::MAX,
            old(self).cpu_list.wf(),
            forall|va:VAddr| #![auto] dom0_address_space.get_pagetable_mapping().dom().contains(va) ==> (
                page_ptr_valid(dom0_address_space.get_pagetable_mapping()[va] as usize)
                &&
                va != 0
                &&
                boot_page_ptrs@[page_ptr2page_index(dom0_address_space.get_pagetable_mapping()[va] as usize) as int].0 == MAPPED && boot_page_ptrs@[page_ptr2page_index(dom0_address_space.get_pagetable_mapping()[va] as usize) as int].1 == va
                ),
            forall|page_ptr:PagePtr| #![auto] dom0_address_space.get_pagetable_page_closure().contains(page_ptr) ==> 
                (
                    page_ptr_valid(page_ptr)
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].0 == PAGETABLE
                ),
            forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == PAGETABLE ==>
                dom0_address_space.get_pagetable_page_closure().contains(page_index2page_ptr(i)),

        ensures
            self.kernel_wf(),
        {
            self.proc_man.init();
            self.page_alloc.init(boot_page_ptrs, boot_page_perms);
            self.pcid_alloc.init(dom0_address_space, kernel_pml4_entry);
            assert(self.kernel_page_mapping_wf());
            self.cpu_list.init_to_none();
            assert(self.kernel_no_transit_thread());
            assert(self.kernel_cpulist_wf());
            assert(self.proc_man.wf());
            
            proof{
                page_ptr_lemma();
            }
            assert(forall|page_ptr:PagePtr| #![auto] dom0_address_space.get_pagetable_page_closure().contains(page_ptr) ==> self.page_alloc.get_page_table_pages().contains(page_ptr));
            assert(forall|page_ptr:PagePtr| #![auto] self.page_alloc.get_page_table_pages().contains(page_ptr) ==> dom0_address_space.get_pagetable_page_closure().contains(page_ptr));
            assert(self.page_alloc.get_page_table_pages() =~= self.pcid_alloc.get_page_table_pages());
            assert(self.page_alloc.get_allocated_pages() =~= self.proc_man.page_closure());
            assert(self.page_alloc.mem_wf());

            let num_free_pages = self.page_alloc.get_num_free_pages();

            if num_free_pages >= 2{
                let (page_ptr_1, page_perm_1) = self.page_alloc.alloc_kernel_mem();
                let (page_ptr_2, page_perm_2) = self.page_alloc.alloc_kernel_mem();

                // assert(self.page_alloc.get_allocated_pages() =~= Set::<PagePtr>::empty().insert(page_ptr_1).insert(page_ptr_2));

                assert(page_ptr_1 != page_ptr_2);
                assert(self.proc_man.scheduler.len() == 0);
                let dom0_proc_ptr = self.proc_man.new_proc(page_ptr_1, page_perm_1, 0);
                let dom0_thread_ptr = self.proc_man.new_thread(page_ptr_2, page_perm_2, dom0_proc_ptr);
                // assert(self.proc_man.page_closure() =~= Set::<PagePtr>::empty().insert(page_ptr_1).insert(page_ptr_2));
            }

            assert(self.page_alloc.get_page_table_pages() =~= self.pcid_alloc.get_page_table_pages());
            
            assert(self.page_alloc.get_allocated_pages() =~= self.proc_man.page_closure());
            assert(self.page_alloc.mem_wf());

            assert(self.kernel_page_mapping_wf());
            assert(self.kernel_no_transit_thread());
            assert(self.kernel_cpulist_wf());
            assert(self.proc_man.wf());
        }

        

    // pub open spec fn kernel_page_closure(&self) -> Set<PagePtr>
    // {
    //     self.proc_man.page_closure()
    //     +
    //     self.pcid_alloc.page_closure()
    //     // + 
    //     // ... add page_closure of other kernel component
    // }

    // pub open spec fn system_data_page_closure(&self) -> Set<PagePtr>
    // {
    //     //system_data_page_closure() equals to data page closures of all the processes
    //     self.pcid_alloc.data_page_closure()
    // }

    pub open spec fn kernel_mem_wf(&self) -> bool
    {
        &&&
        self.page_alloc.get_page_table_pages() =~= self.pcid_alloc.get_page_table_pages()
        &&&
        self.page_alloc.get_allocated_pages() =~= self.proc_man.page_closure()
        &&&
        self.page_alloc.mem_wf()
    }

    // pub open spec fn kernel_pcid_wf(&self) -> bool
    // {
    //     &&&
    //     self.proc_man.pcid_closure() =~= self.pcid_alloc.allocated_pcids()
    //     &&&
    //     self.pcid_alloc.pcid_wf()
    // }


    // /TODO: @Xiangdong change variable names when we have the real names ready.
    // /For each Process 'p' and its virtual space 'v', for each '(va,pa)' mapping exists in it's pagetable, 
    // /the ghost set that represents all existing mapping of this 'pa': page_alloc.mappings() -> Set<(vspace,va)> in PA contains such ('v','va') pair 
    // /This help us to reason about the correctness of the rf_counter for each mapped page.
    // /Steps of mapping a physical page (pa) to a new vspace and va,
    // /1. go to the page table of vspace and resolve va. Make sure resolve(vspace,va) is not equals to page_alloc. This ensures that the mapping set of pa does not contain '(vspace,va)' (external body check)
    // /2. map pa into '(vspace,va)', increment rf_counter of pa by 1, and insert '(vspace,va)' into the page_alloc.mappings().
    // /3. we know that page_alloc.mappings() did not contain '(vspace,va)', therefore the length of page_alloc.mappings() is increased by 1 correctly.
    // /It's worth noting that there's no way to actually find all the content of page_alloc.mappings(), without scanning the all the pagetables in the system,
    // /page_alloc.mappings() is just here to help other proofs. 
    // /If page_alloc.rf_count drops to zero, we can infer that no process maps pa anymore without even looking these processes' pagetable
    // /Therefore, page_alloc.mappings() cannot be generated on the fly. (or maybe we can)
    pub open spec fn kernel_page_mapping_wf(&self) -> bool{
        forall |pcid:Pcid, va:VAddr| #![auto] 0<=pcid<PCID_MAX && self.pcid_alloc.get_address_space(pcid).dom().contains(va) ==>
            (
                self.page_alloc.get_page_mappings(self.pcid_alloc.get_address_space(pcid)[va] as usize).contains((pcid,va))
            )
    }

    ///Spec for the tlbs for all the CPUs in the system
    ///If a Pcid is free, meaning that no process is using it, tlb contains no entry for this Pcid (this requires a flushing when freeing a Pcid)
    ///If a Pcid is allocated, meaning exactly one process is using it, the tlb entries agree to the Pcid's pagetable entries
    ///TODO: @Xiangdong, When we have a better representation of the mapping, change agrees() to less_than() to represent that as long as 
    ///the tlb entries have no permission or less permission than the current pagetable, we are good to go. 
    // pub open spec fn kernel_tlb_wf(&self) -> bool{
    //     &&&
    //     (
    //         forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.free_pcids().contains(pcid) ==> (
    //                 self.cpu_list@[i].get_tlb_for_pcid(pcid) =~= Map::empty()
    //         )
    //     )
    //     &&&
    //     (
    //         forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.allocated_pcids().contains(pcid) ==> (
    //                 self.cpu_list@[i].get_tlb_for_pcid(pcid).agrees(self.pcid_alloc.get_va2pa_mapping_for_pcid(pcid))
    //         )
    //     )
    // }

    pub open spec fn kernel_cpulist_wf(&self) -> bool{
        &&&
        (
            self.cpu_list.wf()
        )
        &&&
        (
            forall|i:CPUID,j:CPUID| #![auto] 0<=i<NUM_CPUS && 0<=j<NUM_CPUS && i != j && self.cpu_list@[i as int].is_idle() == false && self.cpu_list@[j as int].is_idle() == false 
                ==> self.cpu_list@[i as int].get_current_thread().unwrap() != self.cpu_list@[j as int].get_current_thread().unwrap()
        )
        &&&
        (
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS && self.cpu_list@[i as int].is_idle() == false ==> self.proc_man.get_thread_ptrs().contains(self.cpu_list@[i as int].get_current_thread().unwrap())
        )
        &&&
        (
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS && self.cpu_list@[i as int].is_idle() == false ==> self.proc_man.get_thread(self.cpu_list@[i as int].get_current_thread().unwrap()).state == RUNNING //RUNNING
        )
    }

    pub open spec fn kernel_no_transit_thread(&self) -> bool
    {
        forall|thread_ptr:ThreadPtr| #![auto] self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> self.proc_man.get_thread(thread_ptr).state != TRANSIT
    }

    pub open spec fn kernel_wf(&self) -> bool
    {
        &&&
        self.kernel_mem_wf()
        // &&&
        // self.kernel_tlb_wf()
        &&&
        self.kernel_no_transit_thread()
        &&&
        self.kernel_cpulist_wf()
        &&&
        self.proc_man.wf()
    }
}
}