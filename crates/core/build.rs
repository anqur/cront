use std::env::var;

fn main() {
    println!("cargo:rustc-env=CC_TARGET={}", var("TARGET").unwrap());
}
