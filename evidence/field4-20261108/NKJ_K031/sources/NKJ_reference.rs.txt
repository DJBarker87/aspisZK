use super::*;
fn NKJ_add(a:u32,b:u32)->u32 {let s=a+b;if s>=P {s-P}else{s}}
pub fn NKJ_channels(q:[u32;4])->[[u32;3];3] {
 let a=NKJ_add(q[0],q[2]);let b=NKJ_add(q[1],q[3]);
 [[q[0],q[1],NKJ_add(q[0],q[1])],[q[2],q[3],NKJ_add(q[2],q[3])],[a,b,NKJ_add(a,b)]]
}
pub fn NKJ_product(a:u32,b:u32)->u64 {a as u64 * b as u64}
pub fn NKJ_row(s:[u64;3],l:[u32;3],r:[u32;3])->[u64;3] {
 [s[0]+NKJ_product(l[0],r[0]),s[1]+NKJ_product(l[1],r[1]),s[2]+NKJ_product(l[2],r[2])]
}
pub fn NKJ_accumulate(s:[[u64;3];3],l:[u32;4],r:[u32;4])->[[u64;3];3] {
 let l=NKJ_channels(l);let r=NKJ_channels(r);
 [NKJ_row(s[0],l[0],r[0]),NKJ_row(s[1],l[1],r[1]),NKJ_row(s[2],l[2],r[2])]
}
fn NKJ_words(q:QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
pub fn NKJ_small2(l:[QM31;2],r:[QM31;2])->QM31 {
 let s=NKJ_accumulate([[0;3];3],NKJ_words(l[0]),NKJ_words(r[0]));
 let s=NKJ_accumulate(s,NKJ_words(l[1]),NKJ_words(r[1]));
 qm31_from_karatsuba_channel_sums(s)
}
pub fn NKJ_small3(l:[QM31;3],r:[QM31;3])->QM31 {
 let s=NKJ_accumulate([[0;3];3],NKJ_words(l[0]),NKJ_words(r[0]));
 let s=NKJ_accumulate(s,NKJ_words(l[1]),NKJ_words(r[1]));
 let s=NKJ_accumulate(s,NKJ_words(l[2]),NKJ_words(r[2]));
 qm31_from_karatsuba_channel_sums(s)
}
pub fn NKJ_small4(l:[QM31;4],r:[QM31;4])->QM31 {
 let s=NKJ_accumulate([[0;3];3],NKJ_words(l[0]),NKJ_words(r[0]));
 let s=NKJ_accumulate(s,NKJ_words(l[1]),NKJ_words(r[1]));
 let s=NKJ_accumulate(s,NKJ_words(l[2]),NKJ_words(r[2]));
 let s=NKJ_accumulate(s,NKJ_words(l[3]),NKJ_words(r[3]));
 qm31_from_karatsuba_channel_sums(s)
}
