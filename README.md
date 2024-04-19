# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

We use [Nix](https://nixos.org) to manage development dependencies.
Install Nix with the following command:

```bash
# Using https://github.com/DeterminateSystems/nix-installer
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

You can now build and run Atmosphere with `cd kernel && cargo run`.

## Atmo

Atmosphere builds with `atmo`, a build system that extends Cargo.
Run `atmo help` for more information.


## Boot on real hardware

* Copy the bootable binaries. If you have built with `debug` mode, look for the
  below binaries under the `debug` directory instead of `release`.

```bash
sudo cp target/x86_64-unknown-none/release/aloader /boot/
cat target/x86_64-unknown-aloader/release/{kernel,dom0} | sudo tee /boot/atmo >/dev/null
```

* Add menuentry to grub.cfg (`/boot/grub/grub.cfg`)

```
menuentry "Atmosphere" {
  set root=(hd0,msdos1)
  echo "Loading Atmosphere..."
  multiboot2 /boot/aloader
  module2 /boot/atmo atmo
  boot
}
```

* Update grub and reboot to select Atmo from the grub menu

```bash
sudo update-grub && sudo reboot
```

## TODO

Remove transit state for threads @Xiangdong.

Move per CPU cache to MMU Manager @Xiangdong.

Optimize PtRegs Copying for syscall @Xiangdong.