//! ELF utilities.
//!
//! Adapted from <https://github.com/nix-community/nix-ld-rs>.
//! Copyright (c) 2023 Zhaofeng Li and nix-ld-rs contributors

use core::ffi::c_void;
use core::fmt;
use core::mem;
use core::ptr;
use core::slice;

use cfg_match::cfg_match;
use displaydoc::Display;
use plain::Plain;

cfg_match! {
    target_pointer_width = "64" => {
        use goblin::elf64 as elf_types;
        const EM_SELF: u16 = elf_types::header::EM_X86_64;
    }
    target_pointer_width = "32" => {
        use goblin::elf32 as elf_types;
        const EM_SELF: u16 = elf_types::header::EM_386;
    }
}

use elf_types::{
    header::{Header, ET_DYN},
    program_header::{ProgramHeader, PT_LOAD, PF_R, PF_W, PF_X},
};

const HEADER_SIZE: usize = mem::size_of::<Header>();

#[derive(Display, Debug)]
pub enum Error {
    /// Binary not long enough to have an ELF header
    TooShort,

    /// Binary is not an ELF
    BadMagic,

    /// Binary is for wrong architecture (expected 0x{expected:x}, got 0x{actual:x})
    WrongArchitecture {
        expected: u16,
        actual: u16,
    },

    /// Binary is not relocatable
    NotRelocatable,

    /// Binary has bad program header size {0}
    BadProgramHeaderSize(usize),

    /// No loadable segments
    NoLoadableSegments,

    /// Failed to memory map
    MapFailed,
}

pub trait Memory {
    // TODO: Higher-level abstractions, move to ainterface

    /// Maps anonymous memory.
    ///
    /// If base is null, then the mapping can be at an arbitary address.
    unsafe fn map_anonymous(&mut self, base: *mut c_void, size: usize, protection: PageProtection) -> *mut c_void;
}

pub struct ElfHandle {
    elf: &'static [u8],
    header: Header,
    ph_size: usize,
    page_size: usize,
}

pub struct ElfMapping {
    pub load_bias: usize,
    pub entry_point: *const c_void,
}

struct ProgramHeaders<'a> {
    data: &'a [u8],
    entry_size: usize,
    num_entries: usize,
}

struct ProgramHeadersIter<'ph, 'a> {
    headers: &'ph ProgramHeaders<'a>,
    index: usize,
}
struct DisplayPFlags<'ph>(&'ph ProgramHeader);

#[derive(Debug, Clone)]
struct LoadableSummary {
    total_mapping_size: usize,
    first_vaddr: usize,
}

trait ProgramHeaderExt {
    fn prot_flags(&self) -> PageProtection;
}

#[derive(Debug, Clone, Copy)]
pub struct PageProtection {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl ElfHandle {
    pub fn parse(elf: &'static [u8], page_size: usize) -> Result<Self, Error> {
        let header_bytes = elf[..HEADER_SIZE]
            .try_into()
            .map_err(|_| Error::TooShort)?;

        let header = Header::from_bytes(header_bytes);
        if &header.e_ident[..4] != b"\x7fELF".as_slice() {
            return Err(Error::BadMagic);
        }

        if header.e_machine != EM_SELF {
            return Err(Error::WrongArchitecture {
                expected: EM_SELF,
                actual: header.e_machine,
            });
        }

        if header.e_type != ET_DYN {
            // We only support PIE kernels
            return Err(Error::NotRelocatable);
        }

        let ph_size = header.e_phentsize as usize * header.e_phnum as usize;
        if ph_size == 0 || ph_size > 65536 {
            return Err(Error::BadProgramHeaderSize(ph_size));
        }

        Ok(Self {
            elf,
            header: header.clone(),
            ph_size,
            page_size,
        })
    }

    pub fn load(self, memory: &mut impl Memory) -> Result<ElfMapping, Error> {
        let phs = self.program_headers();
        let summary = if let Some(summary) = phs.summarize_loadable() {
            summary
        } else {
            return Err(Error::NoLoadableSegments);
        };

        log::info!("Program headers:");
        for ph in phs.iter() {
            log::info!("- {:?}", ph);
        }

        // This assumes that the ELF is relocatable
        let load_addr = unsafe {
            memory.map_anonymous(
                ptr::null_mut(),
                self.page_align(summary.total_mapping_size),
                PageProtection {
                    read: false,
                    write: false,
                    execute: false,
                },
            )
        };

        if load_addr.is_null() {
            return Err(Error::MapFailed);
        }

        // The first section's code starts at
        //
        //     load_addr + page_offset(ph.p_vaddr)
        let load_bias = (load_addr as usize).wrapping_sub(self.page_start(summary.first_vaddr));
        let entry_point = (load_bias + self.header.e_entry as usize) as *const c_void;

        log::debug!("   Total Size: 0x{:x}", summary.total_mapping_size);
        log::debug!("    Load Addr: {:x?}", load_addr);
        log::debug!("  First Vaddr: 0x{:x?}", summary.first_vaddr);
        log::debug!("    Load Bias: 0x{:x?}", load_bias);
        log::debug!("  Entry Point: 0x{:x?}", entry_point);
        log::debug!("    Page Size: {}", self.page_size);

        log::debug!(
            "GDB: add-symbol-file /path/to/elf 0x{:x}",
            load_bias
        );

        for ph in phs.iter() {
            if ph.p_type != PT_LOAD || ph.p_memsz == 0 {
                continue;
            }

            let memsz = ph.p_memsz as usize;
            let filesz = ph.p_filesz as usize;
            let vaddr = ph.p_vaddr as usize;
            let vend = vaddr + memsz;
            let fend = vaddr + filesz;
            let offset = ph.p_offset as usize;

            let prot = ph.prot_flags();

            let total_map_size = self.page_align(vend) - self.page_start(vaddr);
            let file_map_size =
                self.page_align(core::cmp::min(fend, vend)) - self.page_start(vaddr);

            // There can very well be a section with filesz == 0
            if file_map_size > 0 {
                // Assumption:
                //
                //     page_offset(ph.p_vaddr) == page_offset(ph.p_offset)
                //
                // We do the following mmap for the file-backed portion:
                let mapping = unsafe {
                    let addr = self.page_start(load_bias + vaddr);
                    let size = file_map_size;

                    log::trace!(
                        "mmap [{ph}] [0x{addr:x}-0x{mend:x}] (vaddr=0x{vaddr:x}, offset=0x{offset:x})",
                        mend = addr + size,
                        ph = DisplayPFlags(ph),
                    );

                    memory.map_anonymous(
                        addr as *mut c_void,
                        size,
                        prot,
                    )
                };

                if mapping.is_null() {
                    log::error!("Failed to map segment 0x{:x}", vaddr);
                    return Err(Error::MapFailed);
                }

                // FIXME: Unwritable memory
                let dst = unsafe { slice::from_raw_parts_mut(mapping as *mut u8, file_map_size) };
                let src = &self.elf[self.page_start(offset)..self.page_start(offset) + file_map_size];
                dst.copy_from_slice(src);
            }

            // Memory beyond memsz is zero-initialized
            if memsz > filesz && (ph.p_flags & PF_W != 0) {
                // Zero out the fractional page
                let zero_addr = load_bias + vaddr + filesz;
                let zero_end = self.page_align(zero_addr);
                if zero_end > zero_addr {
                    let fractional_page = unsafe { slice::from_raw_parts_mut(zero_addr as *mut u8, zero_end - zero_addr) };
                    fractional_page.fill(0);
                }

                if file_map_size < total_map_size {
                    let mapping = unsafe {
                        let addr = load_addr.add(file_map_size);
                        let size = total_map_size - file_map_size;
                        log::trace!(
                            "mmap [{ph}] [{addr:?}-0x{mend:x}] (vaddr=0x{vaddr:x}, anon)",
                            mend = addr as usize + size,
                            ph = DisplayPFlags(ph),
                        );

                        memory.map_anonymous(addr, size, prot)
                    };

                    if mapping.is_null() {
                        log::error!("Failed to map anonymous portion for segment 0x{:x}", vaddr);
                        return Err(Error::MapFailed);
                    }
                }
            }
        }

        Ok(ElfMapping {
            load_bias,
            entry_point,
        })
    }

    fn program_headers(&self) -> ProgramHeaders<'static> {
        let data = &self.elf[HEADER_SIZE..HEADER_SIZE + self.ph_size];
        ProgramHeaders {
            data,
            entry_size: self.header.e_phentsize as usize,
            num_entries: self.header.e_phnum as usize,
        }
    }

    #[inline(always)]
    fn page_align(&self, v: usize) -> usize {
        (v + self.page_size - 1) & !(self.page_size - 1)
    }

    #[inline(always)]
    fn page_start(&self, v: usize) -> usize {
        v & !(self.page_size - 1)
    }
}

impl<'a> ProgramHeaders<'a> {
    pub fn iter(&'a self) -> ProgramHeadersIter<'a, 'a> {
        ProgramHeadersIter {
            headers: self,
            index: 0,
        }
    }

    pub fn summarize_loadable(&self) -> Option<LoadableSummary> {
        let mut first_vaddr = None;
        let mut addr_min = usize::MAX;
        let mut addr_max = usize::MIN;

        for ph in self.iter() {
            if ph.p_type != PT_LOAD || ph.p_memsz == 0 {
                continue;
            }

            if first_vaddr.is_none() {
                first_vaddr = Some(ph.p_vaddr as usize);
            }

            if addr_min > ph.p_vaddr as usize {
                addr_min = ph.p_vaddr as usize;
            }

            let vend = ph.p_vaddr as usize + ph.p_memsz as usize;
            if addr_max < vend {
                addr_max = vend;
            }
        }

        first_vaddr.map(|first_vaddr| LoadableSummary {
            first_vaddr,
            total_mapping_size: addr_max - addr_min,
        })
    }
}

impl<'ph, 'a> Iterator for ProgramHeadersIter<'ph, 'a> {
    type Item = &'ph ProgramHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.headers.num_entries {
            return None;
        }

        let base = self.index * self.headers.entry_size;
        let bytes = &self.headers.data[base..base + self.headers.entry_size];
        let entry = <ProgramHeader as Plain>::from_bytes(bytes).unwrap();

        self.index += 1;

        Some(entry)
    }
}

impl ProgramHeaderExt for ProgramHeader {
    #[inline(always)]
    fn prot_flags(&self) -> PageProtection {
        let p_flags = &self.p_flags;
        PageProtection {
            read: p_flags & PF_R != 0,
            write: p_flags & PF_W != 0,
            execute: p_flags & PF_X != 0,
        }
    }
}

impl<'ph> fmt::Display for DisplayPFlags<'ph> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let p_flags = &self.0.p_flags;
        let mut write_prot = |mask, s| {
            if p_flags & mask != 0 {
                write!(f, "{}", s)
            } else {
                write!(f, " ")
            }
        };
        write_prot(PF_R, "R")?;
        write_prot(PF_W, "W")?;
        write_prot(PF_X, "X")?;
        Ok(())
    }
}
