{
  description = "Atmosphere";

  inputs = {
    mars-std.url = "github:mars-research/mars-std";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.flake-utils.follows = "mars-std/flake-utils";
      inputs.flake-compat.follows = "mars-std/flake-compat";
    };
    verus = {
      url = "github:mars-research/verus/mars";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.flake-utils.follows = "mars-std/flake-utils";
      inputs.flake-compat.follows = "mars-std/flake-compat";
      inputs.crane.follows = "crane";
    };
  };

  outputs = { self, mars-std, crane, verus, ... }: let
    supportedSystems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
  in mars-std.lib.eachSystem supportedSystems (system: let
    pkgs = mars-std.legacyPackages.${system};
    inherit (pkgs) lib;
    x86Pkgs = mars-std.legacyPackages.x86_64-linux;
    x86Tools = pkgs.pkgsCross.gnu64;

    pinnedRust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
    rustPlatform = pkgs.makeRustPlatform {
      rustc = pinnedRust;
      cargo = pinnedRust;
    };

    craneLib = (crane.mkLib pkgs).overrideToolchain pinnedRust;

    mkShell = pkgs.mkShell.override {
      stdenv = pkgs.llvmPackages_14.stdenv;
    };

    mkCargoShim = sub: pkgs.writeShellScriptBin "cargo-${sub}" ''
      shift 1
      exec atmo ${sub} "$@"
    '';
  in {
    devShell = mkShell {
      nativeBuildInputs = [
        pinnedRust

        pkgs.mars-research.mars-tools

        verus.packages.${system}.verus
      ] ++ (with pkgs; [
        llvmPackages_14.bintools
        llvmPackages_14.llvm

        cargo-expand cargo-outdated cargo-edit

        pkg-config

        util-linuxMinimal

        nasm

        gdb

        qemu

        editorconfig-checker

        (pkgs.writeShellScriptBin "x86_64.ld" ''
          exec ${x86Tools.buildPackages.bintools}/bin/${x86Tools.stdenv.cc.targetPrefix}ld "$@"
        '')

        (pkgs.writeShellScriptBin "atmo" ''
          set -euo pipefail
          root=$(dirname $(cargo locate-project --workspace | ${pkgs.jq}/bin/jq -r .root))
          pushd "$root/build-tool" >/dev/null
          exec cargo run --quiet -- "$@"
        '')

        (mkCargoShim "verify")
        (mkCargoShim "gdb")
      ]);

      buildInputs = [ pkgs.openssl ];

      RUSTC_BOOTSTRAP = "1";

      # Used by build-tool
      GRUB_X86_MODULES = "${x86Pkgs.grub2}/lib/grub/i386-pc";
      QBOOT_BIOS = "${x86Pkgs.qboot}/bios.bin";
    };
  });
}
