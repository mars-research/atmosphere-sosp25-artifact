use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::page::*;
use crate::pcid_alloc::{PcidAllocator,PCID_MAX};
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;

verus! {
pub const NUM_CPUS:usize = 32;

pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub pcid_alloc: PcidAllocator,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
}

impl MarsArray<Cpu,NUM_CPUS>{
    pub fn init_to_none(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].is_idle(),
    {
        let mut i = 0;
        while i != NUM_CPUS
            invariant
                0<= i <= NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<i ==> self@[j].current_t.is_None() && self@[j].tlb@ =~= Map::empty() ,
            ensures
                i == NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<NUM_CPUS ==> self@[j].current_t.is_None() && self@[j].tlb@ =~= Map::empty() ,
        {
            let cpu = Cpu{
                current_t: None,
                tlb: Ghost(Map::empty()),
            };
            let tmp:Ghost<Seq<Cpu>> = Ghost(self@); 
            self.set(i,cpu);
            assert(self.seq@ =~= tmp@.update(i as int, cpu));
            i = i + 1;
        }
    }
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
            ret.pcid_alloc.page_table_ptrs.wf(),
            ret.pcid_alloc.page_table_perms@ =~= Map::empty(),
            ret.cpu_list.wf(),
    {
        let ret = Self {
            proc_man : ProcessManager::new(),
            page_alloc: PageAllocator::new(),
            pcid_alloc: PcidAllocator::new(),
            cpu_list: MarsArray::<Cpu,NUM_CPUS>::new(),
        };

        ret
    }

     

    pub fn kernel_init(&mut self,boot_page_ptrs: &ArrayVec<bool,NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>)
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
            old(self).page_alloc.allocated_pages@ =~= Set::empty(),
            old(self).page_alloc.mapped_pages@ =~= Set::empty(),
            old(self).page_alloc.available_pages@ =~= Set::empty(),
            old(self).page_alloc.page_perms@.dom() =~= Set::empty(),
            old(self).pcid_alloc.page_table_ptrs.wf(),
            old(self).pcid_alloc.page_table_perms@ =~= Map::empty(),
            boot_page_ptrs.wf(),
            boot_page_ptrs.len() == NUM_PAGES,
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int] == true ==> 
                (boot_page_perms@.dom().contains(page_index2page_ptr(i))
                 && 
                 boot_page_perms@[page_index2page_ptr(i)]@.pptr == page_index2page_ptr(i)
                 &&
                 boot_page_perms@[page_index2page_ptr(i)]@.value.is_Some()
                )
            ),
            NUM_PAGES * 4096 <= usize::MAX,
            old(self).cpu_list.wf()
        ensures
            self.kernel_wf(),
        {
            self.proc_man.init();
            self.page_alloc.init(boot_page_ptrs, boot_page_perms);
            self.pcid_alloc.init();
            self.cpu_list.init_to_none();
            assert(self.kernel_no_transit_thread());
            assert(self.kernel_cpulist_wf());
            assert(self.proc_man.wf());
        }

        

    pub closed spec fn kernel_page_closure(&self) -> Set<PagePtr>
    {
        self.proc_man.page_closure()
        +
        self.pcid_alloc.page_closure()
        // + 
        // ... add page_closure of other kernel component
    }

    pub closed spec fn system_data_page_closure(&self) -> Set<PagePtr>
    {
        //system_data_page_closure() equals to data page closures of all the processes
        self.pcid_alloc.data_page_closure()
    }

    pub closed spec fn kernel_mem_wf(&self) -> bool
    {
        &&&
        self.kernel_page_closure() =~= self.page_alloc.allocated_pages()
        &&&
        self.system_data_page_closure() =~= self.page_alloc.mapped_pages()
        &&&
        self.page_alloc.mem_wf()
    }

    pub closed spec fn kernel_pcid_wf(&self) -> bool
    {
        &&&
        self.proc_man.pcid_closure() =~= self.pcid_alloc.allocated_pcids()
        &&&
        self.pcid_alloc.pcid_wf()
    }


    ///TODO: @Xiangdong change variable names when we have the real names ready.
    ///For each Process 'p' and its virtual space 'v', for each '(va,pa)' mapping exists in it's pagetable, 
    ///the ghost set that represents all existing mapping of this 'pa': page_alloc.mappings() -> Set<(vspace,va)> in PA contains such ('v','va') pair 
    ///This help us to reason about the correctness of the rf_counter for each mapped page.
    ///Steps of mapping a physical page (pa) to a new vspace and va,
    ///1. go to the page table of vspace and resolve va. Make sure resolve(vspace,va) is not equals to page_alloc. This ensures that the mapping set of pa does not contain '(vspace,va)' (external body check)
    ///2. map pa into '(vspace,va)', increment rf_counter of pa by 1, and insert '(vspace,va)' into the page_alloc.mappings().
    ///3. we know that page_alloc.mappings() did not contain '(vspace,va)', therefore the length of page_alloc.mappings() is increased by 1 correctly.
    ///It's worth noting that there's no way to actually find all the content of page_alloc.mappings(), without scanning the all the pagetables in the system,
    ///page_alloc.mappings() is just here to help other proofs. 
    ///If page_alloc.rf_count drops to zero, we can infer that no process maps pa anymore without even looking these processes' pagetable
    ///Therefore, page_alloc.mappings() cannot be generated on the fly. (or maybe we can)
    pub closed spec fn kernel_page_mapping_wf(&self) -> bool{
        forall |page_ptr:PagePtr| #![auto] self.page_alloc.mapped_pages().contains(page_ptr) ==>
            (
                forall|pcid: Pcid| #![auto] 0<=pcid<PCID_MAX && self.pcid_alloc.all_pcids().contains(pcid) ==>
                    (
                        forall|va:VAddr,pa:PAddr| #![auto] self.pcid_alloc.get_va2pa_mapping_for_pcid(pcid).contains_pair(va,pa) && pa == page_ptr ==>
                            (
                                self.page_alloc.page_mappings(page_ptr).contains((pcid,va))
                            )
                    )
            )
        //true
    }

    ///Spec for the tlbs for all the CPUs in the system
    ///If a Pcid is free, meaning that no process is using it, tlb contains no entry for this Pcid (this requires a flushing when freeing a Pcid)
    ///If a Pcid is allocated, meaning exactly one process is using it, the tlb entries agree to the Pcid's pagetable entries
    ///TODO: @Xiangdong, When we have a better representation of the mapping, change agrees() to less_than() to represent that as long as 
    ///the tlb entries have no permission or less permission than the current pagetable, we are good to go. 
    pub closed spec fn kernel_tlb_wf(&self) -> bool{
        &&&
        (
            forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.free_pcids().contains(pcid) ==> (
                    self.cpu_list@[i].get_tlb_for_pcid(pcid) =~= Map::empty()
            )
        )
        &&&
        (
            forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.allocated_pcids().contains(pcid) ==> (
                    self.cpu_list@[i].get_tlb_for_pcid(pcid).agrees(self.pcid_alloc.get_va2pa_mapping_for_pcid(pcid))
            )
        )
    }

    pub closed spec fn kernel_cpulist_wf(&self) -> bool{
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

    pub closed spec fn kernel_no_transit_thread(&self) -> bool
    {
        forall|thread_ptr:ThreadPtr| #![auto] self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> self.proc_man.get_thread(thread_ptr).state != TRANSIT
    }

    pub closed spec fn kernel_wf(&self) -> bool
    {
        // &&&
        // self.kernel_mem_wf()
        // &&&
        // self.kernel_tlb_wf()
        &&&
        self.kernel_no_transit_thread()
        &&&
        self.kernel_cpulist_wf()
        &&&
        self.proc_man.wf()
    }


    pub fn sys_timer_int(&mut self, cpu_id: CPUID)
        requires
            old(self).kernel_wf(),
            0 <= cpu_id <NUM_CPUS,
            old(self).proc_man.scheduler.len() < MAX_NUM_THREADS,
    {
        assert(0 <= cpu_id <NUM_CPUS);
        let thread_ptr_option = self.cpu_list.get(cpu_id).current_t;
        if thread_ptr_option.is_none(){
            //should panic as unverified code has some fatal bugs
            return;
        }
        let thread_ptr = thread_ptr_option.unwrap();
        assert(self.proc_man.get_thread(thread_ptr).state == RUNNING);
        assert(self.proc_man.get_thread(thread_ptr).state != SCHEDULED);
        self.proc_man.push_scheduler(thread_ptr);

        let new_thread_ptr = self.proc_man.pop_scheduler();
        assert(self.proc_man.scheduler@.contains(new_thread_ptr) == false);

        let cpu = Cpu{
            current_t: Some(new_thread_ptr),
            tlb: self.cpu_list.get(cpu_id).tlb
        };

        self.cpu_list.set(cpu_id,cpu);
        assert(self.cpu_list.wf());
        assert(self.kernel_cpulist_wf());
        assert(self.proc_man.wf());
        assert(self.kernel_wf());
    }

    /// Send Do Not Wait syscall
    /// syscall will success if and only if
    pub fn sys_send_no_wait(&mut self, cpu_id: CPUID, sender_endpoint_index: EndpointIdx)
        requires
            old(self).kernel_wf(),
            0 <= cpu_id <NUM_CPUS,
            // old(self).proc_man.scheduler.len() < MAX_NUM_THREADS,
    {
        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
            //put error code here
            return;
        } 
        assert(0<=sender_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS);

        assert(0 <= cpu_id <NUM_CPUS);
        let sender_thread_ptr_option = self.cpu_list.get(cpu_id).current_t;
        if sender_thread_ptr_option.is_none(){
            //should panic as unverified code has some fatal bugs
            return;
        }
        let sender_thread_ptr = sender_thread_ptr_option.unwrap();
        assert(self.proc_man.get_thread(sender_thread_ptr).state == RUNNING);
        assert(self.proc_man.get_thread(sender_thread_ptr).state != SCHEDULED);
        // assert(self.proc_man.get_thread(sender_thread_ptr).state != BLOCKED);
        // assert(self.proc_man.scheduler@.contains(sender_thread_ptr) == false);

        let endpoint_ptr = self.proc_man.get_thread_endpoint_descriptor(sender_thread_ptr, sender_endpoint_index);
        if endpoint_ptr == 0 {
            //put error code here
            return;
        }
        assert(endpoint_ptr != 0);
        assert(self.proc_man.get_endpoint_ptrs().contains(endpoint_ptr));

        let endpoint_len = self.proc_man.get_endpoint_len(endpoint_ptr);
        if endpoint_len == 0{
            // no receiver
            return;
        }
        //assert(self.proc_man.get_endpoint(self.proc_man.get_thread(sender_thread_ptr).endpoint_descriptors@[sender_endpoint_index as int]).len() != 0);

        let endpoint_queue_state = self.proc_man.get_endpoint_queue_state(endpoint_ptr);
        if endpoint_queue_state == SEND{
            //sender queue
            return; // due to no wait
        }

        assert(endpoint_len > 0 && endpoint_queue_state == RECEIVE);

        let sender_endpoint_payload = self.proc_man.get_thread_endpoint_payload(sender_thread_ptr);

        let receiver_thread_ptr = self.proc_man.get_endpoint_queue_head(endpoint_ptr);
        let receiver_endpoint_payload = self.proc_man.get_thread_endpoint_payload(receiver_thread_ptr);
        assert(self.proc_man.get_thread(receiver_thread_ptr).state == BLOCKED);
        assert(sender_thread_ptr != receiver_thread_ptr);

        if sender_endpoint_payload.is_none() && receiver_endpoint_payload.is_none(){
            //just context switch and schedule sender
            assert(self.kernel_wf());
            if self.proc_man.scheduler.len() >= MAX_NUM_THREADS{
                //no space in scheduler 
                return;
            }

            assert(self.proc_man.scheduler.len() < MAX_NUM_THREADS);
            self.proc_man.set_thread_to_transit(sender_thread_ptr);

            let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
            assert(tmp == receiver_thread_ptr);

            self.proc_man.push_scheduler(sender_thread_ptr);
            assert(self.proc_man.get_thread(tmp).state == TRANSIT);
            self.proc_man.set_thread_to_running(receiver_thread_ptr);

            let cpu = Cpu{
                current_t: Some(receiver_thread_ptr),
                tlb: self.cpu_list.get(cpu_id).tlb
            };
    
            self.cpu_list.set(cpu_id,cpu);
            assert(self.kernel_wf());

            return;
        }

        if sender_endpoint_payload.is_some() && receiver_endpoint_payload.is_some()
        {

            let sender_endpoint_payload_index = sender_endpoint_payload.unwrap();
            let receiver_endpoint_payload_index = receiver_endpoint_payload.unwrap();

            let endpoint_ptr = self.proc_man.get_thread_endpoint_descriptor(sender_thread_ptr, sender_endpoint_payload_index);
            if endpoint_ptr == 0{
                // sender trying to send a endpoint that does not exist
                return;
            }

            let endpoint_rf = self.proc_man.get_endpoint_rf_counter(endpoint_ptr);
            if endpoint_rf == usize::MAX{
                // endpoint cannot be shared anymore, counter overflow. (not gonna happe)
                return;
            }

            if self.proc_man.scheduler.len() >= MAX_NUM_THREADS{
                //no space in scheduler 
                return;
            }

            
            let receiver_capable_of_receiving = self.proc_man.check_thread_capable_for_new_endpoint(receiver_thread_ptr, receiver_endpoint_payload_index, endpoint_ptr);
            if receiver_capable_of_receiving == false{
                //receiver no longer able to receive, goes to scheduler
                let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
                assert(tmp == receiver_thread_ptr);
                self.proc_man.push_scheduler(receiver_thread_ptr);

                assert(self.kernel_wf());
                return;
            }
            
            self.proc_man.pass_endpoint(sender_thread_ptr,sender_endpoint_payload_index,receiver_thread_ptr,receiver_endpoint_payload_index);
            assert(self.proc_man.scheduler.len() < MAX_NUM_THREADS);
            self.proc_man.set_thread_to_transit(sender_thread_ptr);

            let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
            assert(tmp == receiver_thread_ptr);

            self.proc_man.push_scheduler(sender_thread_ptr);
            assert(self.proc_man.get_thread(tmp).state == TRANSIT);
            self.proc_man.set_thread_to_running(receiver_thread_ptr);

            let cpu = Cpu{
                current_t: Some(receiver_thread_ptr),
                tlb: self.cpu_list.get(cpu_id).tlb
            };
    
            self.cpu_list.set(cpu_id,cpu);
            assert(self.kernel_wf());

            return;
        }
    }
}

}