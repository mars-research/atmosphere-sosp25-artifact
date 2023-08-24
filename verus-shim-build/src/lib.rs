pub fn setup() {
    println!("cargo:rustc-cfg=verus_macro_erase_ghost");
    println!("cargo:rustc-cfg=verus_shim");
}
