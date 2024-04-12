use core::mem;

use aelf::ElfHandle;
use astd::io::Cursor;

use crate::elf::Mapper;

pub const DOM1_BASE: usize = 0xb0_0000_0000;
pub const DOM1_ELF: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/dom1.elf"));

pub fn test_dom1(payload: &[u8]) {
    log::info!("Length of Dom1 ELF: {}", payload.len());

    let cursor = Cursor::new(payload);
    let mut mapper = Mapper::new(DOM1_BASE);
    let elf = ElfHandle::parse(cursor, 4096).unwrap();
    let (map, _) = elf.load(&mut mapper).unwrap();

    log::info!("Loaded dom1: {:#x?}", map);

    let entry: extern "C" fn() = unsafe { mem::transmute(map.entry_point) };

    log::info!("Calling dom1");
    // FIXME: Switch stack
    entry();
    log::info!("Returned from dom1");
}


pub fn spawn_dom1(payload: &[u8]) {
    log::info!("Length of dom1 ELF: {}", payload.len());

    unsafe{
        let cursor = Cursor::new(payload);
        let mut mapper = Mapper::new(DOM1_BASE);
        let elf = ElfHandle::parse(cursor, 4096).unwrap();
        let (map, _) = elf.load(&mut mapper).unwrap();
    
        log::info!("Loaded dom1: {:?}", map);
    
        let entry: extern "C" fn() = unsafe { mem::transmute(map.entry_point) };
    
        let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }

        let new_stack = map.load_addr + map.load_size;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }
        let rsp: usize = new_stack + size/2;
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,entry as *const () as usize, rsp, map.load_addr, (map.load_size + size) / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        return;
    }
}
