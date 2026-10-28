use aspis_core::field::{QM31,CM31,M31};
fn check(w:[u32;4]) {
 let x=QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}};
 let mut actual=[0xa5u8;16];x.write_le_bytes(&mut actual);
 let expected=core::array::from_fn::<_,16,_>(|i|(w[i/4]>>(8*(i%4)))as u8);
 assert_eq!(actual,expected);
}
fn main(){let mut n=0;for i in 0..4 {for j in 0..4 {for v in 0..=255{let mut w=[0xdeadbeef;4];w[i]=(v as u32)<<(8*j);check(w);n+=1;}}}for w in [0,1,u32::MAX,0x7fffffff,0x80000000]{check([w;4]);n+=1;}println!("FINITE V198: {n} write_le_bytes pairs, all16bytes, raw noncanonical carriers retained");}
