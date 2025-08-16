# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

We use [Nix](https://nixos.org) to manage development dependencies.
Install Nix with the following command:

```bash
# Using https://github.com/DeterminateSystems/nix-installer
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

After installing nix, enter nix shell. The environment will be set up automatically.

```bash
nix develop
```

## Build and Run on QEMU (with KVM)
Build and run on QEMU

```
atmo run --release
```
Build and run on QEMU with KVM

```
atmo run --release --kvm
```

## Verification

Verify the OS kernel. On a powerful machine, this should take only 15 seconds. 
```
atmo verify
```

Obtain line counts for verification
```
./get_line_count.sh
```

Obtain verification time for each function
```
./get_verification_time.sh
```
## Boot on real hardware
* Build the kernel with `atmo run` 

* Copy the bootable binaries. If you have built with `debug` mode, look for the
  below binaries under the `debug` directory instead of `release`.

```bash
sudo cp target/x86_64-unknown-none/release/aloader /boot/
cat target/x86_64-unknown-aloader/release/{kernel,dom0} | sudo tee /boot/atmo >/dev/null
```

* Add menuentry to grub.cfg (`/boot/grub/grub.cfg`)

```
menuentry "Atmosphere" {
  set root=(hd0,gpt3)
  echo "Loading Atmosphere..."
  multiboot2 /boot/aloader
  module2 /boot/atmo atmo
  boot
}
```

* Reboot and selet Atmo from the grub menu

```bash
sudo reboot
```

* System calls microbenchmark results should show up in the end
