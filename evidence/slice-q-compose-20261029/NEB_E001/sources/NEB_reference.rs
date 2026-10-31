const P:u32=0x7fff_ffff;
pub fn reference(x:u64)->u32 {
 let x=(x & P as u64).wrapping_add(x >> 31u32);
 let x=(x & P as u64).wrapping_add(x >> 31u32);
 let x=x as u32;
 if x>=P {x.wrapping_sub(P)}else{x}
}
