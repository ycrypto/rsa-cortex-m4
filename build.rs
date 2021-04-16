fn main() {
    #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
    println!("cargo:rustc-cfg=feature=\"u64\"");
    #[cfg(all(target_pointer_width = "32", not(feature = "u64")))]
    println!("cargo:rustc-cfg=feature=\"u32\"");
}
