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
