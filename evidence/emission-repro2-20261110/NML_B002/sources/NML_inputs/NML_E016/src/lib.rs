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
pub fn add_word_ref(a:u32,b:u32)->u32{let s=a+b;if s>=0x7fff_ffff{s-0x7fff_ffff}else{s}}
pub fn add_ref(a:Q,b:Q)->Q {Q{c0:C{a:add_word_ref(a.c0.a,b.c0.a),b:add_word_ref(a.c0.b,b.c0.b)},c1:C{a:add_word_ref(a.c1.a,b.c1.a),b:add_word_ref(a.c1.b,b.c1.b)}}}
pub fn initial_ref(withdraw:bool,a:Q,b:Q,c:Q)->(Q,Q,Q,Q){let zero=lift_ref(0);if withdraw{(zero,add_ref(add_ref(a,b),c),zero,zero)}else{(a,zero,add_ref(a,b),c)}}
pub fn scalar_ref(withdraw:bool,present:bool,input:Q,output:Q,private_term:Q,withdraw_term:Q)->[Q;2]{let out=if withdraw{if present{add_ref(output,withdraw_term)}else{output}}else{add_ref(output,private_term)};[input,out]}
pub fn copy_variant_ref(withdraw:bool)->bool {if withdraw {true} else {false}}
