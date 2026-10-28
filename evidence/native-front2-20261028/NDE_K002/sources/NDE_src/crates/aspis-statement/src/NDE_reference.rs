#[derive(Clone, Copy, PartialEq, Eq)]
pub struct C { pub a: u32, pub b: u32 }
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Q { pub c0: C, pub c1: C }
pub fn lift_ref(value: u32) -> Q {
    Q { c0: C { a: value, b: 0 }, c1: C { a: 0, b: 0 } }
}
pub fn extension_limbs_ref(value: Q) -> [u32;4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}
