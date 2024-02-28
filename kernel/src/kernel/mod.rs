use astd::sync::Mutex;
use verified::kernel::Kernel;
use verified::proc::ProcessManager;
use verified::mmu::MMUManager;
use verified::page_alloc::PageAllocator;
use core::mem::size_of;

static KERNEL: Mutex<Option<Kernel>> = Mutex::new(None);

pub fn kernel_test(){
    log::info!("hello from kernel");
}

pub fn kernel_new(){
    log::info!("kernel lock aquiring\n");
    log::info!("kernel size={:?}",size_of::<Kernel>());
    log::info!("proc_man size={:?}",size_of::<ProcessManager>());
    log::info!("mmu_man size={:?}",size_of::<MMUManager>());
    log::info!("page_alloc size={:?}",size_of::<PageAllocator>());
    
    let mut my_int = KERNEL.lock();
    log::info!("kernel lock aquired");
    // *my_int = Some(Kernel::new());
}