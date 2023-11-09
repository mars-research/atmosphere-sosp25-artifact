#![deny(unused_must_use)]

extern crate nasm_rs;

macro_rules! source {
    ($($arg:tt)*) => {
        println!("cargo:rerun-if-changed={}", format_args!($($arg)*));
    };
}

fn main() {
    println!("Baking garlic bread...");
    source!("build.rs");

    // TODO: Re-add multiboot2 boot path to aloader
    //x86_64_asm("multiboot2_header.asm");
    //x86_64_asm("crt0.asm");
}

fn x86_64_asm(source: &str) {
    let arch_dir = "src/boot";
    source!("{}/{}", arch_dir, source);

    let mut mb = nasm_rs::Build::new();
    mb.file(&format!("{}/{}", arch_dir, source));
    mb.target("");
    mb.flag("-felf64");

    let objects = mb.compile_objects().unwrap();
    for object in objects {
        println!("cargo:rustc-link-arg={}", object.to_str().unwrap());
    }
}
