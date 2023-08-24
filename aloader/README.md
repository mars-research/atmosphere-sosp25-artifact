# Early Loader

The Early Loader is responsible for setting up memory and loading the microkernel and the initial domain.
This is akin to the [Elfloader](https://docs.sel4.systems/projects/elfloader) in seL4.

After control is handed off to the kernel, other domains can subsequently be loaded and launched the initial domain.

## Boot Protocols

The loader supports booting from the following protocols:

- Multiboot 2
- [Xen x86/HVM Direct Boot ABI](https://xenbits.xen.org/docs/unstable/misc/pvh.html)
    - This is for booting from QEMU using the Direct Linux Boot functionality. Atmosphere cannot be used as a Xen guest yet.
    - QEMU [refuses](https://patchwork.ozlabs.org/project/qemu-devel/patch/20100819112414.GH22245@os.inf.tu-dresden.de) to load 64-bit Multiboot binaries with its `-kernel` flag, and cannot seem to correctly relocate 64-bit ELF.

## Boot Process

- The Early Loader is started via one of the supported boot protocols, with the microkernel image as well as the first domain passed in.
    - The last bootloader is responsible for loading the ELF images of the kernel and the first domain into memory as plain binary, no relocations.
- The Early Loader computes the usable memory regions.

## Initial Allocator

In order to load the microkernel and the first
