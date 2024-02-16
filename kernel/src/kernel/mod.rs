use astd::sync::Mutex;
use verified::kernel::Kernel;

static KERNEL: Mutex<Option<Kernel>> = Mutex::new(None);

pub fn kernel_test(){
    log::info!("hello from kernel");
}

pub fn kernel_new(){
    log::info!("kernel lock aquiring\n");
    let mut my_int = KERNEL.lock();
    log::info!("kernel lock aquired");
    *my_int = Some(Kernel::new());
}