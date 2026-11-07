#![allow(dead_code)]
pub fn reduce_u62_ref(x:u64)->u32 { let y=(x & 2147483647)+(x>>31u32);let z=(y & 2147483647)+(y>>31u32);let w=z as u32;if w>=2147483647 {w-2147483647}else{w} }
pub fn m31_neg_ref(x:u32)->u32 {if x==0 {0}else{2147483647-x}}
pub fn cm31_from_ref(x:u32)->[u32;2] {[x,0]}
pub fn cm31_neg_ref(x:[u32;2])->[u32;2] {[m31_neg_ref(x[0]),m31_neg_ref(x[1])]}
pub fn qm31_neg_ref(x:[u32;4])->[u32;4] {[m31_neg_ref(x[0]),m31_neg_ref(x[1]),m31_neg_ref(x[2]),m31_neg_ref(x[3])]}
pub fn qm31_zero_ref(x:[u32;4])->bool { x[0]==0 && x[1]==0 && x[2]==0 && x[3]==0 }
pub fn bits_ref(eight:bool)->u32 {if eight {3}else{1}}
pub fn index_ref(x:&[u32;16],i:usize)->u32 {x[i]}
fn add_ref(x:u32,y:u32)->u32 {let s=x+y;if s>=2147483647{s-2147483647}else{s}}
pub fn prepared_ref(x:[u32;4])->[[u32;3];3] {let row0=[x[0],x[1],add_ref(x[0],x[1])];let row1=[x[2],x[3],add_ref(x[2],x[3])];let a=add_ref(x[0],x[2]);let b=add_ref(x[1],x[3]);[row0,row1,[a,b,add_ref(a,b)]]}
fn sub_ref(x:u32,y:u32)->u32 {let s=x+2147483647-y;if s>=2147483647{s-2147483647}else{s}}
fn reconstruct_ref(x:[u64;3])->[u32;2] {let a=reduce_u62_ref(x[0]);let b=reduce_u62_ref(x[1]);let c=reduce_u62_ref(x[2]);[sub_ref(a,b),sub_ref(sub_ref(c,a),b)]}
fn cadd_ref(x:[u32;2],y:[u32;2])->[u32;2]{[add_ref(x[0],y[0]),add_ref(x[1],y[1])]}
fn csub_ref(x:[u32;2],y:[u32;2])->[u32;2]{[sub_ref(x[0],y[0]),sub_ref(x[1],y[1])]}
fn byr_ref(x:[u32;2])->[u32;2]{[sub_ref(add_ref(x[0],x[0]),x[1]),add_ref(x[0],add_ref(x[1],x[1]))]}
pub fn channels_ref(sums:[[u64;3];3])->[u32;4]{let m0=reconstruct_ref(sums[0]);let m1=reconstruct_ref(sums[1]);let m2=reconstruct_ref(sums[2]);let a=cadd_ref(m0,byr_ref(m1));let b=csub_ref(csub_ref(m2,m0),m1);[a[0],a[1],b[0],b[1]]}
pub fn value_ref(x:&[[u8;32];16],i:usize)->[u8;32]{x[i]}
pub fn root_ref(x:&[[u8;32];16],root:&[u8;32])->bool{x[0]==*root}
pub fn guard_ref(s2:bool,folds:usize,first:bool,second:bool)->bool{s2 && folds==2 && first && second}
pub fn wide_neg_ref(x:[u32;8])->[u32;8]{[m31_neg_ref(x[0]),m31_neg_ref(x[1]),m31_neg_ref(x[2]),m31_neg_ref(x[3]),m31_neg_ref(x[4]),m31_neg_ref(x[5]),m31_neg_ref(x[6]),m31_neg_ref(x[7])]}
pub fn pack_ref(v:[[u32;4];4])->[u32;4]{
 let p=2147483647u64;let v0=v[0];let v1=v[1];let v2=v[2];let v3=v[3];
 let a=v0[0] as u64+(p-v1[1] as u64)+2*v2[2] as u64+(p-v2[3] as u64)+(p-v3[2] as u64)+(2*p-2*v3[3] as u64);
 let b=v0[1] as u64+v1[0] as u64+v2[2] as u64+2*v2[3] as u64+2*v3[2] as u64+(p-v3[3] as u64);
 let c=v0[2] as u64+(p-v1[3] as u64)+v2[0] as u64+(p-v3[1] as u64);
 let d=v0[3] as u64+v1[2] as u64+v2[1] as u64+v3[0] as u64;
 [reduce_u62_ref(a),reduce_u62_ref(b),reduce_u62_ref(c),reduce_u62_ref(d)]
}
pub fn raw_pack_ref(v:[[u32;4];4],which:usize)->u64{
 let p=2147483647u64;let v0=v[0];let v1=v[1];let v2=v[2];let v3=v[3];
 if which==0 {v0[0] as u64+(p-v1[1] as u64)+2*v2[2] as u64+(p-v2[3] as u64)+(p-v3[2] as u64)+(2*p-2*v3[3] as u64)}
 else if which==1 {v0[1] as u64+v1[0] as u64+v2[2] as u64+2*v2[3] as u64+2*v3[2] as u64+(p-v3[3] as u64)}
 else if which==2 {v0[2] as u64+(p-v1[3] as u64)+v2[0] as u64+(p-v3[1] as u64)}
 else {v0[3] as u64+v1[2] as u64+v2[1] as u64+v3[0] as u64}
}
