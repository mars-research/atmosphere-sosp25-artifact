use core::mem;

use aelf::ElfHandle;
use astd::io::Cursor;

use crate::elf::Mapper;

pub const DOM1_BASE: usize = 0xb0_0000_0000;
pub const DOM1_ELF: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/dom1.elf"));

pub fn test_dom1() {
    log::info!("Length of dom1 ELF: {}", DOM1_ELF.len());

    let cursor = Cursor::new(DOM1_ELF);
    let mut mapper = Mapper::new(DOM1_BASE);
    let elf = ElfHandle::parse(cursor, 4096).unwrap();
    let (map, _) = elf.load(&mut mapper).unwrap();

    log::info!("Loaded dom1: {:?}", map);

    let entry: extern "C" fn() = unsafe { mem::transmute(map.entry_point) };

    log::info!("Calling dom1");
    // FIXME: Switch stack
    entry();
    log::info!("Returned from dom1");
}
