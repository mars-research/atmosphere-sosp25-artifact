use pcid::pci::{Pci, PciClass};
use pcid::utils::PciDevice;

use alloc::format;
use alloc::vec::Vec;
use lazy_static::lazy_static;
use spin::Mutex;

lazy_static! {
    pub static ref PCI_DEVICES: Mutex<Vec<PciDevice>> = Mutex::new(Vec::new());
}

fn handle_parsed_header(pci_dev: &PciDevice) {
    let header = &pci_dev.pci_hdr.hdr;
    let raw_class: u8 = header.class().into();
    let (bus_num, dev_num, func_num) = &pci_dev.pci_addr.into();
    let mut string = format!(
        "PCI {:>02X}/{:>02X}/{:>02X} {:>04X}:{:>04X} {:>02X}.{:>02X}.{:>02X}.{:>02X} {:?}",
        bus_num,
        dev_num,
        func_num,
        header.vendor_id(),
        header.device_id(),
        raw_class,
        header.subclass(),
        header.interface(),
        header.revision(),
        header.class()
    );

    match header.class() {
        PciClass::Storage => match header.subclass() {
            0x01 => {
                string.push_str(" IDE");
            }
            0x06 => {
                string.push_str(" SATA");
            }
            _ => (),
        },
        PciClass::SerialBus => match header.subclass() {
            0x03 => match header.interface() {
                0x00 => {
                    string.push_str(" UHCI");
                }
                0x10 => {
                    string.push_str(" OHCI");
                }
                0x20 => {
                    string.push_str(" EHCI");
                }
                0x30 => {
                    string.push_str(" XHCI");
                }
                _ => (),
            },
            _ => (),
        },
        _ => (),
    }

    for (i, bar) in header.bars().iter().enumerate() {
        if !bar.is_none() {
            string.push_str(&format!("\n\tbar[{}] => {}", i, bar.unwrap()));
        }
    }

    log::info!("{}", string);
}

pub fn scan_pci_devs() {
    //print!("PCI BS/DV/FN VEND:DEVI CL.SC.IN.RV\n");

    let pci = Pci::new();
    let mut pci_devices = PCI_DEVICES.lock();
    for bus in pci.buses() {
        for dev in bus.devs() {
            for func in dev.funcs() {
                let func_num = func.num;
                match pcid::utils::get_config(bus.num, dev.num, func_num) {
                    Ok(pci_dev) => {
                        handle_parsed_header(&pci_dev);
                        pci_devices.push(pci_dev);
                    }
                    Err(_) => {}
                }
            }
        }
    }
}
