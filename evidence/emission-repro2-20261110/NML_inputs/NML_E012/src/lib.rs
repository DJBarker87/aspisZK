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
pub fn reduce_ref(x:u64)->u32 {
    let x=(x & 0x7fff_ffff)+(x >> 31u32);
    let x=(x & 0x7fff_ffff)+(x >> 31u32);
    let x=x as u32;
    if x>=0x7fff_ffff {x-0x7fff_ffff} else {x}
}
pub fn extension_raw_ref(limbs:[u64;4])->Q {
    Q{c0:C{a:reduce_ref(limbs[0]),b:reduce_ref(limbs[1])},c1:C{a:reduce_ref(limbs[2]),b:reduce_ref(limbs[3])}}
}
