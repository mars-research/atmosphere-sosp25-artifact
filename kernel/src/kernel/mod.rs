use astd::sync::Mutex;
use verified::kernel::Kernel;
use verified::proc::ProcessManager;
use verified::mmu::MMUManager;
use verified::page_alloc::PageAllocator;
use core::mem::size_of;
use verified::array_vec::ArrayVec as vArrayVec;
use verified::pagetable::PageTable as vPageTable;
use verified::pagetable::PageEntry as vPageEntry;
use verified::proc::IPCPayLoad as vIPCPayLoad;
use verified::define::PagePerm;
use verified::define::PagePtr;
use verified::trap::PtRegs as vPtRegs;
use verified::proc::Process;
use verified::proc::Thread;
use verified::proc::Endpoint;
use verified::mars_staticlinkedlist::Node;
use astd::heapless::Vec as ArrayVec;
use astd::boot::PhysicalMemoryType;
use core::arch::asm;
static KERNEL: Mutex<Option<Kernel>> = Mutex::new(None);

use vstd::prelude::*;

use verified::define as vdefine;

trait PhysicalMemoryTypeExt {
    fn to_verified_page_state(&self) -> vdefine::PageState;
}

impl PhysicalMemoryTypeExt for PhysicalMemoryType {
    fn to_verified_page_state(&self) -> vdefine::PageState {
        match self {
            Self::Available => vdefine::FREE,
            Self::Domain => vdefine::MAPPED,
            Self::PageTable => vdefine::PAGETABLE,
            Self::Kernel | Self::Reserved => vdefine::UNAVAILABLE,
        }
    }
}


pub fn kernel_test(){
    log::info!("hello from kernel");
}

pub fn kernel_new(){
    log::info!("kernel lock aquiring\n");
    log::info!("kernel size={:?}",size_of::<Kernel>());
    log::info!("proc_man size={:?}",size_of::<ProcessManager>());
    log::info!("mmu_man size={:?}",size_of::<MMUManager>());
    log::info!("page_alloc size={:?}",size_of::<PageAllocator>());
    
    log::info!("process size={:?}",size_of::<Process>());    
    log::info!("thread size={:?}",size_of::<Thread>());    
    log::info!("endpoint size={:?}",size_of::<Endpoint>());
    log::info!("Node size={:?}",size_of::<Node>());
    let mut my_int = KERNEL.lock();
    log::info!("kernel lock aquired");
    *my_int = Some(Kernel::new());
}

pub fn kernel_test_ipc_send_message(dom0_pagetable_ptr: usize){
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(0,vPtRegs::new_empty());
    log::info!("pop dom0 \n {:?} \n",dom0_retstruc);
    let dom0_endpoint_ret = KERNEL.lock().as_mut().unwrap().syscall_new_endpoint(0,vPtRegs::new_empty(), 0);
    log::info!("new endpoint \n {:?} \n",dom0_endpoint_ret);
    let (dom0_proc_ret,proc_ptr_op, thread_ptr_op) = KERNEL.lock().as_mut().unwrap().syscall_new_proc(0,vPtRegs::new_empty(), 0, vPtRegs::new_empty());
    log::info!("new proc \n {:?} \n",dom0_proc_ret);
    let dom1_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(1,vPtRegs::new_empty());
    log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);
    // log::info!("{:x?}",proc_ptr_op.unwrap());
    // log::info!("{:x?}",thread_ptr_op.unwrap());
    let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(0,vPtRegs::new_empty(), 0xA000000000, vdefine::READ_WRITE_EXECUTE, 1);

    let mut user_value:usize = 0;
    unsafe {
        log::info!("write 0xA000000000");
        *(0xA000000000 as * mut usize) = 0x233;
        log::info!("read 0xA000000000");
        user_value = *(0xA000000000 as * const usize);
    }
    log::info!("*0xA000000000 = {:x?}",user_value);

    let dom1_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(1,vPtRegs::new_empty(), 0xA000000000, vdefine::READ_WRITE_EXECUTE, 1);

    let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
    dom0_ipc_pay_load.message = Some((0xA000000000,8));
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(0,vPtRegs::new_empty(),0,dom0_ipc_pay_load);
    log::info!("send ret value {:?}",dom0_retstruc);
    let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
    dom1_ipc_pay_load.message = Some((0xA000000000,8));
    let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(1,vPtRegs::new_empty(),0,dom1_ipc_pay_load);
    log::info!("receive ret value {:?}",dom1_retstruc);

    let pop_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(0,vPtRegs::new_empty());
    log::info!("pop scheduler ret value {:?}",pop_retstruc);

    let new_pcid = KERNEL.lock().as_mut().unwrap().proc_man.get_pcid_by_thread_ptr(thread_ptr_op.unwrap());
    log::info!("new_pcid {:x?}",new_pcid);
    let new_cr3 = KERNEL.lock().as_mut().unwrap().mmu_man.get_cr3_by_pcid(new_pcid);
    log::info!("new_cr3 {:x?}",new_cr3);

    log::info!("switching to new cr3");
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) new_cr3 => _,
        );
    }
    log::info!("hello from new cr3");

    let mut user_value:usize = 0;
    unsafe {
        // log::info!("read 0xA000000000");
        user_value = *(0xA000000000 as * const usize);
    }
    log::info!("*0xA000000000 = {:x?}",user_value);

    log::info!("switching to old cr3");
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) dom0_pagetable_ptr => _,
        );
    }
    log::info!("hello from old cr3");



    log::info!("end of new ipc test");
}

pub fn kernel_test_ipc_send_pages(dom0_pagetable_ptr: usize){
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(0,vPtRegs::new_empty());
    log::info!("pop dom0 \n {:?} \n",dom0_retstruc);
    let dom0_endpoint_ret = KERNEL.lock().as_mut().unwrap().syscall_new_endpoint(0,vPtRegs::new_empty(), 0);
    log::info!("new endpoint \n {:?} \n",dom0_endpoint_ret);
    let (dom0_proc_ret,proc_ptr_op, thread_ptr_op) = KERNEL.lock().as_mut().unwrap().syscall_new_proc(0,vPtRegs::new_empty(), 0, vPtRegs::new_empty());
    log::info!("new proc \n {:?} \n",dom0_proc_ret);
    
    // log::info!("{:x?}",proc_ptr_op.unwrap());
    // log::info!("{:x?}",thread_ptr_op.unwrap());
    let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(0,vPtRegs::new_empty(), 0xA000000000, vdefine::READ_WRITE_EXECUTE, 1);
    log::info!("dom0 malloc 1 page at 0xA000000000 \n {:?} \n",dom0_malloc_ret);
    let mut user_value:usize = 0;
    unsafe {
        log::info!("write 0xA000000000");
        *(0xA000000000 as * mut usize) = 0x233;
        log::info!("read 0xA000000000");
        user_value = *(0xA000000000 as * const usize);
    }
    log::info!("*0xA000000000 = {:x?}",user_value);

    let mut user_pml4:usize = 0;
    unsafe{
        user_pml4 = *((dom0_pagetable_ptr + (((0xA000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml4 {:x?}",user_pml4);

    let mut user_pml3:usize = 0;
    unsafe{
        user_pml3 = *(( (user_pml4 & 0xFFFFFFFFF000) + (((0xA000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml3 {:x?}",user_pml3);

    let mut user_pml2:usize = 0;
    unsafe{
        user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000) + (((0xA000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml2 {:x?}",user_pml2);

    let mut user_pml1:usize = 0;
    unsafe{
        user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000) + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml1 {:x?}",user_pml1);

    let mut user_pml0:usize = 0;
    unsafe{
        user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000) + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml0 {:x?}",user_pml0);

    let mut user_pml4:usize = 0;
    unsafe{
        user_pml4 = *((dom0_pagetable_ptr + (((0x8000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml4 {:x?}",user_pml4);

    let mut user_pml3:usize = 0;
    unsafe{
        user_pml3 = *(( (user_pml4 & 0xFFFFFFFFF000) + (((0x8000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml3 {:x?}",user_pml3);

    let mut user_pml2:usize = 0;
    unsafe{
        user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000) + (((0x8000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml2 {:x?}",user_pml2);

    let mut user_pml1:usize = 0;
    unsafe{
        user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000) + (((0x8000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml1 {:x?}",user_pml1);

    let mut user_pml0:usize = 0;
    unsafe{
        user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000) + (((0x8000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml0 {:x?}",user_pml0);


    let dom1_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(1,vPtRegs::new_empty());
    log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);

    let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
    dom1_ipc_pay_load.page_payload = Some((0xA000000000,1));
    let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(1,vPtRegs::new_empty(),0,dom1_ipc_pay_load);
    log::info!("receive ret value {:?}",dom1_retstruc);
    let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
    dom0_ipc_pay_load.page_payload = Some((0xA000000000,1));
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(0,vPtRegs::new_empty(),0,dom0_ipc_pay_load);
    log::info!("send ret value {:?}",dom0_retstruc);

    let pop_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(1,vPtRegs::new_empty());
    log::info!("pop scheduler ret value {:?}",pop_retstruc);

    let new_pcid = KERNEL.lock().as_mut().unwrap().proc_man.get_pcid_by_thread_ptr(thread_ptr_op.unwrap());
    log::info!("new_pcid {:x?}",new_pcid);
    let new_cr3 = KERNEL.lock().as_mut().unwrap().mmu_man.get_cr3_by_pcid(new_pcid);
    log::info!("new_cr3 {:x?}",new_cr3);

    let mut user_pml4:usize = 0;
    unsafe{
        user_pml4 = *((new_cr3 + (((0xA000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml4 {:x?}",user_pml4);

    let mut user_pml3:usize = 0;
    unsafe{
        user_pml3 = *(( (user_pml4 & 0xFFFFFFFFF000) + (((0xA000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml3 {:x?}",user_pml3);

    let mut user_pml2:usize = 0;
    unsafe{
        user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000) + (((0xA000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml2 {:x?}",user_pml2);

    let mut user_pml1:usize = 0;
    unsafe{
        user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000) + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml1 {:x?}",user_pml1);

    let mut user_pml0:usize = 0;
    unsafe{
        user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000) + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8) as * const usize);
    }
    log::info!("user_pml0 {:x?}",user_pml0);

    log::info!("switching to new cr3");
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) new_cr3 => _,
        );
    }
    log::info!("hello from new cr3");

    let mut user_value:usize = 0;
    unsafe {
        // log::info!("read 0xA000000000");
        user_value = *(0xA000000000 as * const usize);
    }
    log::info!("*0xA000000000 = {:x?}",user_value);

    log::info!("switching to old cr3");
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) dom0_pagetable_ptr => _,
        );
    }
    log::info!("hello from old cr3");



    log::info!("end of new ipc test");
}


pub fn kernel_test_new_proc(){
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(0,vPtRegs::new_empty());
    log::info!("pop dom0 \n {:?} \n",dom0_retstruc);
    let dom0_endpoint_ret = KERNEL.lock().as_mut().unwrap().syscall_new_endpoint(0,vPtRegs::new_empty(), 0);
    log::info!("new endpoint \n {:?} \n",dom0_endpoint_ret);
    let (dom0_proc_ret,proc_ptr_op, thread_ptr_op) = KERNEL.lock().as_mut().unwrap().syscall_new_proc(0,vPtRegs::new_empty(), 0, vPtRegs::new_empty());
    log::info!("new proc \n {:?} \n",dom0_proc_ret);
    // log::info!("{:x?}",proc_ptr_op.unwrap());
    // log::info!("{:x?}",thread_ptr_op.unwrap());
    log::info!("end of new proc test");
    
}

pub fn kernel_test_malloc(){
    let dom0_retstruc = KERNEL.lock().as_mut().unwrap().kernel_idle_pop_sched(0,vPtRegs::new_empty());
    log::info!("pop dom0 \n {:?} \n",dom0_retstruc);
    let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(0,vPtRegs::new_empty(), 0xA000000000, vdefine::READ_WRITE_EXECUTE, 1);
    log::info!("dom0 malloc 1 page at 0xA000000000 \n {:?} \n",dom0_malloc_ret);
    let mut user_value:usize = 0;
    unsafe {
        log::info!("write 0xA000000000");
        *(0xA000000000 as * mut usize) = 0x233;
        log::info!("read 0xA000000000");
        user_value = *(0xA000000000 as * const usize);
    }
    log::info!("*0xA000000000 = {:x?}",user_value);
    log::info!("end of malloc test");
}

pub fn kernel_init(boot_page_ptrs: &ArrayVec<(u64,PhysicalMemoryType),{4*1024*1024}>, dom0_pagetable_ptr: usize, kernel_pml4_entry_ptr: usize){

    log::info!("{:p}", verified::kernel::Kernel::syscall_new_proc as *const ());

    let mut boot_pages = vArrayVec::<(u8, usize), {1*1024*1024}>::new();
    let mut i = 0;
    while i != 1*1024*1024 {
        boot_pages.push((boot_page_ptrs[i].1.to_verified_page_state(), boot_page_ptrs[i].0 as usize));
        i = i + 1;
    }
    let dom0_pagetable = vPageTable::new(dom0_pagetable_ptr);
    let kernel_page_entry = vPageEntry{addr:kernel_pml4_entry_ptr, perm: 0x1 as usize};
    let mut dom0_pt_regs = vPtRegs::new_empty();
    dom0_pt_regs.r15 = 233;
    let page_perms:Tracked<Map<PagePtr,PagePerm>> =  Tracked::assume_new();
    let ret_code = KERNEL.lock().as_mut().unwrap().kernel_init(&boot_pages,page_perms,dom0_pagetable,kernel_page_entry, dom0_pt_regs);
    log::info!("kernel init ret_code {:?}",ret_code);
    kernel_test_ipc_send_message(dom0_pagetable_ptr);

    log::info!("End of kernel syscall test \n\n\n\n\n\n");
}