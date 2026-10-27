#![allow(dead_code)]
// Safe references are compiled with the real std/alloc implementation.
fn empty_reference<T>(v: &Vec<T>) -> bool { v.len() == 0 }
fn default_reference<T>() -> Vec<T> { Vec::new() }
fn pop_reference<T>(v: &mut Vec<T>) -> Option<T> {
    if v.len() == 0 { None } else { Some(v.remove(v.len() - 1)) }
}
#[cfg(kani)]
mod checks {
    use super::*;
    #[kani::proof]
    #[kani::unwind(10)]
    fn empty_u8() {
        let n: usize = kani::any(); kani::assume(n <= 8);
        let mut v = Vec::new();
        for _ in 0..n { v.push(kani::any::<u8>()); }
        assert_eq!(v.is_empty(), empty_reference(&v));
    }
    #[kani::proof]
    fn default_u8() {
        assert_eq!(Vec::<u8>::default(), default_reference::<u8>());
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn pop_u8() {
        let n: usize = kani::any(); kani::assume(n <= 8);
        let mut v = Vec::new();
        for _ in 0..n { v.push(kani::any::<u8>()); }
        let mut w = v.clone();
        assert_eq!(v.pop(), pop_reference(&mut w));
        assert_eq!(v,w);
    }
}
