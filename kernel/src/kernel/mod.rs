use astd::boot::PhysicalMemoryType;
use astd::heapless::Vec as ArrayVec;
use astd::sync::Mutex;
use core::arch::asm;
use core::arch::x86_64::_rdtsc;
use core::mem::size_of;
use verified::kernel::Kernel;
use verified::define as vdefine;
use verified::trap::Registers as vRegisters;
use crate::bridge::Bridge;
use verified::bridge::SwitchDecision;
use verified::bridge::TrustedBridge;
use crate::cpu;
static KERNEL: Mutex<Option<Kernel>> = Mutex::new(None);

use vstd::prelude::*;

use verified::process_manager::spec_proof::ProcessManager;
use verified::memory_manager::MemoryManager;
use verified::allocator::page_allocator_spec_impl::PageAllocator;
use verified::process_manager::container::Container;
use verified::process_manager::process::Process;
use verified::process_manager::thread::Thread;
use verified::process_manager::endpoint::Endpoint;
use verified::array_vec::ArrayVec as vArrayVec;
use verified::pagetable::pagemap::PageMap;
use verified::define::PagePerm4k;
use verified::va_range::VaRange4K as vVaRange4K;

use vstd::simple_pptr::PointsTo;

trait PhysicalMemoryTypeExt {
    fn to_verified_page_state(&self) -> vdefine::PageState;
}

impl PhysicalMemoryTypeExt for PhysicalMemoryType {
    fn to_verified_page_state(&self) -> vdefine::PageState {
        match self {
            Self::Available => vdefine::PageState::Free4k,
            Self::Domain => vdefine::PageState::Mapped4k,
            Self::PageTable => vdefine::PageState::Allocated4k,
            Self::Kernel | Self::Reserved => vdefine::PageState::Unavailable4k,
        }
    }
}

pub fn kernel_test() {
    log::info!("hello from kernel");
}

pub fn kernel_new() {
    log::info!("kernel lock aquiring\n");
    log::info!("kernel size={:?}", size_of::<Kernel>());
    log::info!("proc_man size={:?}", size_of::<ProcessManager>());
    log::info!("mmu_man size={:?}", size_of::<MemoryManager>());
    log::info!("page_alloc size={:?}", size_of::<PageAllocator>());

    log::info!("container size={:?}", size_of::<Container>());
    log::info!("process size={:?}", size_of::<Process>());
    log::info!("thread size={:?}", size_of::<Thread>());
    log::info!("endpoint size={:?}", size_of::<Endpoint>());
    // log::info!("Node size={:?}", size_of::<Node>());
    let mut my_int = KERNEL.lock();
    log::info!("kernel lock aquired");
    *my_int = Some(Kernel::new());
}

// pub fn kernel_test_ipc_test_call(dom0_pagetable_ptr: usize) {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 0);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         0,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );
//     let (dom0_proc_ret, proc_ptr_op, thread_ptr_op) = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .syscall_new_proc(0, vRegisters::new_empty(), 0, vRegisters::new_empty());
//     log::info!("new proc \n {:?} \n", dom0_proc_ret);
//     let dom1_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(1, vRegisters::new_empty());
//     log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);
//     let dom1_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         1,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );
//     // log::info!("{:x?}",proc_ptr_op.unwrap());
//     // log::info!("{:x?}",thread_ptr_op.unwrap());

//     let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom0_ipc_pay_load.calling = true;
//     dom0_ipc_pay_load.message = Some((0xA000000000, 8));
//     let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(
//         0,
//         vRegisters::new_empty(),
//         0,
//         dom0_ipc_pay_load,
//     );
//     let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom1_ipc_pay_load.calling = true;
//     dom1_ipc_pay_load.message = Some((0xA000000000, 8));
//     let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(
//         1,
//         vRegisters::new_empty(),
//         0,
//         dom1_ipc_pay_load,
//     );
//     log::info!("send ret value {:?}", dom0_retstruc);
//     log::info!("receive ret value {:?}", dom1_retstruc);

//     let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom1_ipc_pay_load.calling = true;
//     dom1_ipc_pay_load.message = Some((0xA000000000, 8));
//     let dom1_retstruc =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_reply(1, vRegisters::new_empty(), dom1_ipc_pay_load);
//     log::info!("reply ret value {:?}", dom1_retstruc);

//     log::info!("end of new ipc test");
// }

// pub fn kernel_test_ipc_send_endpoint(dom0_pagetable_ptr: usize) {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 0);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 1);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let (dom0_proc_ret, proc_ptr_op, thread_ptr_op) = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .syscall_new_proc(0, vRegisters::new_empty(), 0, vRegisters::new_empty());
//     log::info!("new proc \n {:?} \n", dom0_proc_ret);
//     let dom1_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(1, vRegisters::new_empty());
//     log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);
//     // log::info!("{:x?}",proc_ptr_op.unwrap());
//     // log::info!("{:x?}",thread_ptr_op.unwrap());

//     let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom1_ipc_pay_load.endpoint_payload = Some(1);
//     let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(
//         1,
//         vRegisters::new_empty(),
//         0,
//         dom1_ipc_pay_load,
//     );
//     log::info!("receive ret value {:?}", dom1_retstruc);
//     let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom0_ipc_pay_load.endpoint_payload = Some(1);
//     let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(
//         0,
//         vRegisters::new_empty(),
//         0,
//         dom0_ipc_pay_load,
//     );
//     log::info!("send ret value {:?}", dom0_retstruc);

//     log::info!("end of new ipc test");
// }

// pub fn kernel_test_ipc_send_message(dom0_pagetable_ptr: usize) {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 0);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let (dom0_proc_ret, proc_ptr_op, thread_ptr_op) = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .syscall_new_proc(0, vRegisters::new_empty(), 0, vRegisters::new_empty());
//     log::info!("new proc \n {:?} \n", dom0_proc_ret);
//     let dom1_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(1, vRegisters::new_empty());
//     log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);
//     // log::info!("{:x?}",proc_ptr_op.unwrap());
//     // log::info!("{:x?}",thread_ptr_op.unwrap());
//     let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         0,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );

//     let mut user_value: usize = 0;
//     unsafe {
//         log::info!("write 0xA000000000");
//         *(0xA000000000 as *mut usize) = 0x233;
//         log::info!("read 0xA000000000");
//         user_value = *(0xA000000000 as *const usize);
//     }
//     log::info!("*0xA000000000 = {:x?}", user_value);

//     let dom1_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         1,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );

//     let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom0_ipc_pay_load.message = Some((0xA000000000, 8));
//     let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(
//         0,
//         vRegisters::new_empty(),
//         0,
//         dom0_ipc_pay_load,
//     );
//     log::info!("send ret value {:?}", dom0_retstruc);
//     let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom1_ipc_pay_load.message = Some((0xA000000000, 8));
//     let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(
//         1,
//         vRegisters::new_empty(),
//         0,
//         dom1_ipc_pay_load,
//     );
//     log::info!("receive ret value {:?}", dom1_retstruc);

//     let pop_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop scheduler ret value {:?}", pop_retstruc);

//     let new_pcid = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .proc_man
//         .get_pcid_by_thread_ptr(thread_ptr_op.unwrap());
//     log::info!("new_pcid {:x?}", new_pcid);
//     let new_cr3 = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .mmu_man
//         .get_cr3_by_pcid(new_pcid);
//     log::info!("new_cr3 {:x?}", new_cr3,new_thread_ptr);

//     log::info!("switching to new cr3");
//     unsafe {
//         asm!(
//             "mov cr3, {pml4}",
//             pml4 = inout(reg) new_cr3 => _,
//         );
//     }
//     log::info!("hello from new cr3");

//     let mut user_value: usize = 0;
//     unsafe {
//         // log::info!("read 0xA000000000");
//         user_value = *(0xA000000000 as *const usize);
//     }
//     log::info!("*0xA000000000 = {:x?}", user_value);

//     log::info!("switching to old cr3");
//     unsafe {
//         asm!(
//             "mov cr3, {pml4}",
//             pml4 = inout(reg) dom0_pagetable_ptr => _,
//         );
//     }
//     log::info!("hello from old cr3");

//     log::info!("end of new ipc test");
// }

// pub fn kernel_test_ipc_send_pages(dom0_pagetable_ptr: usize) {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 0);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let (dom0_proc_ret, proc_ptr_op, thread_ptr_op) = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .syscall_new_proc(0, vRegisters::new_empty(), 0, vRegisters::new_empty());
//     log::info!("new proc \n {:?} \n", dom0_proc_ret);

//     // log::info!("{:x?}",proc_ptr_op.unwrap());
//     // log::info!("{:x?}",thread_ptr_op.unwrap());
//     let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         0,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );
//     log::info!(
//         "dom0 malloc 1 page at 0xA000000000 \n {:?} \n",
//         dom0_malloc_ret
//     );
//     let mut user_value: usize = 0;
//     unsafe {
//         log::info!("write 0xA000000000");
//         *(0xA000000000 as *mut usize) = 0x233;
//         log::info!("read 0xA000000000");
//         user_value = *(0xA000000000 as *const usize);
//     }
//     log::info!("*0xA000000000 = {:x?}", user_value);

//     let mut user_pml4: usize = 0;
//     unsafe {
//         user_pml4 = *((dom0_pagetable_ptr
//             + (((0xA000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml4 {:x?}", user_pml4);

//     let mut user_pml3: usize = 0;
//     unsafe {
//         user_pml3 = *(((user_pml4 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml3 {:x?}", user_pml3);

//     let mut user_pml2: usize = 0;
//     unsafe {
//         user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml2 {:x?}", user_pml2);

//     let mut user_pml1: usize = 0;
//     unsafe {
//         user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml1 {:x?}", user_pml1);

//     let mut user_pml0: usize = 0;
//     unsafe {
//         user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml0 {:x?}", user_pml0);

//     let mut user_pml4: usize = 0;
//     unsafe {
//         user_pml4 = *((dom0_pagetable_ptr
//             + (((0x8000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml4 {:x?}", user_pml4);

//     let mut user_pml3: usize = 0;
//     unsafe {
//         user_pml3 = *(((user_pml4 & 0xFFFFFFFFF000)
//             + (((0x8000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml3 {:x?}", user_pml3);

//     let mut user_pml2: usize = 0;
//     unsafe {
//         user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000)
//             + (((0x8000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml2 {:x?}", user_pml2);

//     let mut user_pml1: usize = 0;
//     unsafe {
//         user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000)
//             + (((0x8000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml1 {:x?}", user_pml1);

//     let mut user_pml0: usize = 0;
//     unsafe {
//         user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000)
//             + (((0x8000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml0 {:x?}", user_pml0);

//     let dom1_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(1, vRegisters::new_empty());
//     log::info!("dom1 is running on cpu 1 \n {:?} \n", dom1_retstruc);

//     let mut dom1_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom1_ipc_pay_load.page_payload = Some((0xA000000000, 1));
//     let dom1_retstruc = KERNEL.lock().as_mut().unwrap().syscall_receive_wait(
//         1,
//         vRegisters::new_empty(),
//         0,
//         dom1_ipc_pay_load,
//     );
//     log::info!("receive ret value {:?}", dom1_retstruc);
//     let mut dom0_ipc_pay_load = vIPCPayLoad::new_to_none();
//     dom0_ipc_pay_load.page_payload = Some((0xA000000000, 1));
//     let dom0_retstruc = KERNEL.lock().as_mut().unwrap().syscall_send_wait(
//         0,
//         vRegisters::new_empty(),
//         0,
//         dom0_ipc_pay_load,
//     );
//     log::info!("send ret value {:?}", dom0_retstruc);

//     let pop_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(1, vRegisters::new_empty());
//     log::info!("pop scheduler ret value {:?}", pop_retstruc);

//     let new_pcid = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .proc_man
//         .get_pcid_by_thread_ptr(thread_ptr_op.unwrap());
//     log::info!("new_pcid {:x?}", new_pcid);
//     let new_cr3 = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .mmu_man
//         .get_cr3_by_pcid(new_pcid);
//     log::info!("new_cr3 {:x?}", new_cr3,new_thread_ptr);

//     let mut user_pml4: usize = 0;
//     unsafe {
//         user_pml4 =
//             *((new_cr3 + (((0xA000000000 >> 39) & 0b1_1111_1111u64) as usize) * 8) as *const usize);
//     }
//     log::info!("user_pml4 {:x?}", user_pml4);

//     let mut user_pml3: usize = 0;
//     unsafe {
//         user_pml3 = *(((user_pml4 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 30) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml3 {:x?}", user_pml3);

//     let mut user_pml2: usize = 0;
//     unsafe {
//         user_pml2 = *(((user_pml3 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 21) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml2 {:x?}", user_pml2);

//     let mut user_pml1: usize = 0;
//     unsafe {
//         user_pml1 = *(((user_pml2 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml1 {:x?}", user_pml1);

//     let mut user_pml0: usize = 0;
//     unsafe {
//         user_pml0 = *(((user_pml1 & 0xFFFFFFFFF000)
//             + (((0xA000000000 >> 12) & 0b1_1111_1111u64) as usize) * 8)
//             as *const usize);
//     }
//     log::info!("user_pml0 {:x?}", user_pml0);

//     log::info!("switching to new cr3");
//     unsafe {
//         asm!(
//             "mov cr3, {pml4}",
//             pml4 = inout(reg) new_cr3 => _,
//         );
//     }
//     log::info!("hello from new cr3");

//     let mut user_value: usize = 0;
//     unsafe {
//         // log::info!("read 0xA000000000");
//         user_value = *(0xA000000000 as *const usize);
//     }
//     log::info!("*0xA000000000 = {:x?}", user_value);

//     log::info!("switching to old cr3");
//     unsafe {
//         asm!(
//             "mov cr3, {pml4}",
//             pml4 = inout(reg) dom0_pagetable_ptr => _,
//         );
//     }
//     log::info!("hello from old cr3");

//     log::info!("end of new ipc test");
// }

// pub fn kernel_test_new_proc() {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_endpoint_ret =
//         KERNEL
//             .lock()
//             .as_mut()
//             .unwrap()
//             .syscall_new_endpoint(0, vRegisters::new_empty(), 0);
//     log::info!("new endpoint \n {:?} \n", dom0_endpoint_ret);
//     let (dom0_proc_ret, proc_ptr_op, thread_ptr_op) = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .syscall_new_proc(0, vRegisters::new_empty(), 0, vRegisters::new_empty());
//     log::info!("new proc \n {:?} \n", dom0_proc_ret);
//     // log::info!("{:x?}",proc_ptr_op.unwrap());
//     // log::info!("{:x?}",thread_ptr_op.unwrap());
//     log::info!("end of new proc test");
// }

// pub fn kernel_test_malloc() {
//     let dom0_retstruc = KERNEL
//         .lock()
//         .as_mut()
//         .unwrap()
//         .kernel_idle_pop_sched(0, vRegisters::new_empty());
//     log::info!("pop dom0 \n {:?} \n", dom0_retstruc);
//     let dom0_malloc_ret = KERNEL.lock().as_mut().unwrap().syscall_malloc(
//         0,
//         vRegisters::new_empty(),
//         0xA000000000,
//         vdefine::READ_WRITE_EXECUTE,
//         1,
//     );
//     log::info!(
//         "dom0 malloc 1 page at 0xA000000000 \n {:?} \n",
//         dom0_malloc_ret
//     );
//     let mut user_value: usize = 0;
//     unsafe {
//         log::info!("write 0xA000000000");
//         *(0xA000000000 as *mut usize) = 0x233;
//         log::info!("read 0xA000000000");
//         user_value = *(0xA000000000 as *const usize);
//     }
//     log::info!("*0xA000000000 = {:x?}", user_value);
//     log::info!("end of malloc test");
// }

pub fn kernel_init(
    boot_page_ptrs: &ArrayVec<(u64, PhysicalMemoryType), { 4 * 1024 * 1024 }>,
    dom0_pagetable_ptr: usize,
    kernel_pml4_entry_ptr: usize,
) {

    // log::info!("cpu_list addr {:p}",&(KERNEL.lock().as_ref().unwrap().cpu_list.ar));
    let mut boot_pages = vArrayVec::<(vdefine::PageState, usize), { vdefine::NUM_PAGES }>::new();
    let mut i = 0;

    let mut dom_0_container_ptr = 0;
    let mut dom_0_proc_ptr = 0;
    let mut dom_0_thread_ptr = 0;

    while i !=  vdefine::NUM_PAGES {
        boot_pages.push((
            boot_page_ptrs[i].1.to_verified_page_state(),
            boot_page_ptrs[i].0 as usize,
        ));
        i = i + 1;
    }

    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_container_ptr = boot_pages.get(i).1;
            break;
        }
    }

    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_proc_ptr = boot_pages.get(i).1;
            break;
        }
    }

    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_thread_ptr = boot_pages.get(i).1;
            break;
        }
    }

    log::info!("dom_0_container_ptr {:x?}",dom_0_container_ptr);
    log::info!("dom_0_proc_ptr {:x?}",dom_0_proc_ptr);
    log::info!("dom_0_thread_ptr {:x?}",dom_0_thread_ptr);

    // let dom0_pagetable = vPageTable::new(dom0_pagetable_ptr);
    // let kernel_page_entry = vPageEntry {
    //     addr: kernel_pml4_entry_ptr,
    //     perm: 0x1 as usize,
    // };
    let mut dom0_pt_regs = vRegisters::new_empty();
    dom0_pt_regs.r15 = 233;
    // let page_perms: Tracked<Map<PagePtr, PagePerm>> = Tracked::assume_new();
    // let init_pci_map = vPCIBitMap::new();

    let page_perm_0: Tracked<PagePerm4k> = Tracked::assume_new();
    let page_perm_1: Tracked<PagePerm4k> = Tracked::assume_new();
    let page_perm_2: Tracked<PagePerm4k> = Tracked::assume_new();
    let dom0_page_map_perm: Tracked<PointsTo<PageMap>> = Tracked::assume_new();

    KERNEL.lock().as_mut().unwrap().kernel_init(
        dom_0_container_ptr,
        dom_0_proc_ptr,
        dom_0_thread_ptr,
        &mut boot_pages,
        dom0_pagetable_ptr,
        kernel_pml4_entry_ptr,
        page_perm_0,
        page_perm_1,
        page_perm_2,
        dom0_page_map_perm
    );

    log::info!("dom_0 thread info {:x?}", KERNEL.lock().as_ref().unwrap().get_current_cpu_info(0));
    
    // // log::info!("cpu 0 thread ptr {:?}",KERNEL.lock().as_ref().unwrap().cpu_list.ar[0].current_t);
    // log::info!("kernel init ret_code {:?}", ret_code);
    let dom0_retstruc = KERNEL
    .lock()
    .as_mut()
    .unwrap()
    .schedule_idle_cpu(0, &mut dom0_pt_regs);
    // log::info!("scheduler_return_value {:?}", dom0_retstruc);
    log::info!("dom0 is running on CPU 0");
    // // // kernel_test_ipc_test_call(dom0_pagetable_ptr);
    let pcid_dom0 = 0;
    log::info!("setting dom0's pcid: {:x?}", pcid_dom0);
    let cr3 = dom0_pagetable_ptr | vdefine::PCID_ENABLE_MASK | pcid_dom0;
    // Bridge::set_cr3(cr3 as u64);

    let new_endpoint_retstruc = KERNEL
    .lock()
    .as_mut()
    .unwrap()
    .syscall_new_endpoint(
        dom_0_thread_ptr,
        0,
    );

    match new_endpoint_retstruc.error_code{
        vdefine::RetValueType::SuccessUsize{value:value} => { log::info!{"new endpoint ptr at {:x?}", value}; },
        _ => { log::info!{"new endpoint failed"}; },
    }

    // dom0_test_mmap();

    log::trace!("End of kernel init");
}

pub fn dom0_test_mmap(){
    unsafe{
    let mut kernel = KERNEL.lock();
    let start = _rdtsc();
    let va:usize = 0xC000000000;
    let iter = 5000000;
    log::info!("num of free pages: {:?}",kernel.as_ref().unwrap().page_alloc.free_pages_4k.len());
    for i in 0..iter{

        let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(0);
    
        let ret_struc =  kernel.as_mut().unwrap().syscall_mmap(
            thread_info.0.unwrap(),
            vVaRange4K::new(va + 4096 * i, 1)
        );
        match ret_struc.error_code{
            vdefine::RetValueType::SuccessSeqUsize{..} => { 
            },
            vdefine::RetValueType::VaInUse => { 
                log::info!{"mmap failed at {:?} error: va in use va:{:x?}", i, va + 4096 * i}; 
                break; 
            },
            vdefine::RetValueType::NoQuota => { log::info!{"mmap failed at {:?} error: no quota", i}; break; },
            _ => {},
        }
    }
    
    let end = _rdtsc();
    log::info!("mmap cycle per syscall {:?}",(end-start) as usize /iter);
    log::info!{"mmap test done"};
    }
}

pub extern "C" fn sys_mmap(va:usize, perm_bits:usize, range:usize, regs: &mut vRegisters) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);

    let ret_struc =  kernel.as_mut().unwrap().syscall_mmap(
        thread_info.0.unwrap(),
        vVaRange4K::new(va, range)
    );
    regs.rax = 
        if ret_struc.is_error(){
            log::info!{"sys_mmap failed"};
            1
        }else{
            0
        };
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

// pub extern "C" fn sys_resolve(va:usize,_:usize, _:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_resolve_va(
//         cpu_id,
//         va,
//     );
//     if ret_struc.0.error_code != 0{
//         regs.rax = ret_struc.0.error_code as u64;
//     }
//     else{
//         regs.rax = ret_struc.1 as u64;
//     }
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
// }

// pub extern "C" fn sys_resolve_io(va:usize,_:usize, _:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_resolve_io_va(
//         cpu_id,
//         va,
//     );
//     if ret_struc.0.error_code != 0{
//         regs.rax = ret_struc.0.error_code as u64;
//     }
//     else{
//         regs.rax = ret_struc.1 as u64;
//     }
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
// }


pub extern "C" fn sys_new_endpoint(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let ret_struc =  kernel.as_mut().unwrap().syscall_new_endpoint(
        thread_info.0.unwrap(),
        endpoint_index,
    );
    // regs.rax = ret_struc.error_code as u64;
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

// pub fn sys_new_proc(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters) -> usize{
//     let cpu_id = cpu::get_cpu_id();
//     let new_proc_pt_regs = vRegisters::new_empty();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_proc(
//         cpu_id,
//         endpoint_index,
//         new_proc_pt_regs,
//     );
    
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     ret_struc.0.error_code
// }

// pub fn sys_new_proc_with_iommu(endpoint_index:usize, ip:usize, sp:usize,regs: &mut vRegisters) -> usize{
//     let cpu_id = cpu::get_cpu_id();
//     let new_proc_pt_regs = vRegisters::new_empty();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_proc_with_iommu(
//         cpu_id,
//         endpoint_index,
//         new_proc_pt_regs,
//     );
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     ret_struc.0.error_code
// }

// pub extern "C" fn sys_new_thread(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut new_thread_pt_regs = *regs;
//     new_thread_pt_regs.rip = ip as u64;
//     new_thread_pt_regs.rsp = sp as u64;
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_thread(
//         cpu_id,
//         endpoint_index,
//         new_thread_pt_regs,
//     );
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     regs.rax = ret_struc.0.error_code as u64;
// }

// pub fn sys_send_empty_no_wait(endpoint_index:usize,_:usize, _:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_empty_no_wait(
//         cpu_id,
//         endpoint_index,
//     );
//     drop(kernel);
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     regs.rax = ret_struc.error_code as u64;
// }

// pub extern "C" fn sys_send_empty(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
//     // log::info!("regs {:x?}", regs);
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_empty_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//     );
//     drop(kernel);
//     if ret_struc.0.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             log::info!("no next thread, spin the CPU. TODO: enter the scheduling routine");
//         }
//     }else{
//         if ret_struc.1.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if ret_struc.1.unwrap().1 != ret_struc.0.cr3 {
//                 Bridge::set_cr3((ret_struc.0.cr3 | ret_struc.0.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.0.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.0.error_code as u64;
                
//                 if ret_struc.1.unwrap().2 != ret_struc.0.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

// pub extern "C" fn sys_receive_empty(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     let ret_struc =  kernel.as_mut().unwrap().syscall_receive_empty_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//     );
//     drop(kernel);
//     if ret_struc.0.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             log::info!("no next thread, spin the CPU. TODO: enter the scheduling routine");
//         }
//     }else{
//         if ret_struc.1.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if ret_struc.1.unwrap().1 != ret_struc.0.cr3 {

//                 Bridge::set_cr3((ret_struc.0.cr3 | ret_struc.0.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.0.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.0.error_code as u64;
                
//                 if ret_struc.1.unwrap().2 != ret_struc.0.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

// pub extern "C" fn sys_new_proc_with_iommu_pass_mem(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters, va:usize, range:usize){
//     let cpu_id = cpu::get_cpu_id();
//     let mut new_proc_pt_regs = *regs;
//     new_proc_pt_regs.rip = ip as u64;
//     new_proc_pt_regs.rsp = sp as u64;
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_proc_with_iommu_pass_mem(
//         cpu_id,
//         endpoint_index,
//         new_proc_pt_regs,
//         va,
//         range
//     );
//     regs.rax = ret_struc.0.error_code as u64;
// }

// pub extern "C" fn sched_get_next_thread(regs: &mut vRegisters) -> bool{
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     let ret_struc =  kernel.as_mut().unwrap().kernel_idle_pop_sched(
//         cpu_id,
//         regs,

//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::CPU_ID_INVALID{
//         false
//     }else if ret_struc.error_code == vdefine::CPU_NO_IDLE{
//         false
//     }else if ret_struc.error_code == vdefine::SCHEDULER_EMPTY{
//         false
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("cpu {:?} switching to a new thread/process {:x?} trap frame {:x?} cr3 {:x?}", cpu::get_cpu_id(),ret_struc,regs,ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK);

//             // Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);

//             // let cr3: u64;
//             // unsafe { asm!("mov {cr3}, cr3", cr3 = out(reg) cr3); }
//             Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64 as u64);
//             // log::info!("cr3 {:x?}", cr3);

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{

//                 regs.rax = ret_struc.error_code as u64;

//                 Bridge::set_switch_decision(SwitchDecision::SwitchToClean);

//             }

//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {

//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{

//                 regs.rax = ret_struc.error_code as u64;
                
//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//         true
//     }
// }

// pub extern "C" fn sys_receive_pages(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     // log::info!("cpu_list addr {:p}",&(kernel.as_ref().unwrap().cpu_list.ar));
//     // log::info!("sys_receive_pagestrap frame {:x?} thead_info {:x?} thread{:x?}",regs,thread_info_op,kernel.as_mut().unwrap().cpu_list.ar[cpu_id].current_t, );
//     let ret_struc =  kernel.as_mut().unwrap().syscall_receive_pages_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//         va,
//         range
//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             unsafe{
//                 let has_next_thread = sched_get_next_thread(regs);
//                 if has_next_thread == false{
//                     for i in 0..1000{
//                         asm!("nop");
//                     }
//                 }else{
//                     break;
//                 }
//             }
//         }
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {
//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.error_code as u64;

//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     // log::info!("sys_receive_pages NoSwitching trap frame {:x?}",regs);
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

// pub extern "C" fn sys_send_pages_no_wait(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     // log::info!("regs {:x?}", regs);
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?}",regs,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(0);
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?} thread{:x?}",regs,thread_info_op,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_pages_no_wait(
//         cpu_id,
//         endpoint_index,
//         va,
//         range,
//     );
//     drop(kernel);
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     regs.rax = ret_struc.error_code as u64;
// }

// pub extern "C" fn sys_send_pages(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_pages_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//         va,
//         range
//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             unsafe{
//                 let has_next_thread = sched_get_next_thread(regs);
//                 if has_next_thread == false{
//                     for i in 0..1000{
//                         asm!("nop");
//                     }
//                 }else{
//                     break;
//                 }
//             }
//         }
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {
//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.error_code as u64;

//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

// pub extern "C" fn sys_get_iommu_cr3(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
//     // log::info!("regs {:x?}", regs);
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?}",regs,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(0);
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?} thread{:x?}",regs,thread_info_op,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let (ret_struc,cr3) =  kernel.as_mut().unwrap().syscall_get_iommu_cr3(
//         cpu_id,
//     );
//     drop(kernel);
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     if ret_struc.error_code == verified::define::SUCCESS{
//         regs.rax = cr3 as u64;
//     }else{
//         regs.rax = ret_struc.error_code as u64;
//     }
// }

// pub extern "C" fn sys_iommu_mmap(va:usize, perm_bits:usize, range:usize, regs: &mut vRegisters) {
//     let cpu_id = cpu::get_cpu_id();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_map_pagetable_pages_to_iommutable(
//         cpu_id,
//         va,
//         perm_bits,
//         range,
//     );
//     regs.rax = ret_struc.error_code as u64;
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
// }