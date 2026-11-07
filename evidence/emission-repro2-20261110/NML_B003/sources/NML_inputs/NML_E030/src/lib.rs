#![allow(dead_code)]
pub fn reduce_u62_ref(x:u64)->u32 { let y=(x & 2147483647)+(x>>31);let z=(y & 2147483647)+(y>>31);let w=z as u32;if w>=2147483647 {w-2147483647}else{w} }
pub fn m31_neg_ref(x:u32)->u32 {if x==0 {0}else{2147483647-x}}
pub fn cm31_from_ref(x:u32)->[u32;2] {[x,0]}
pub fn cm31_neg_ref(x:[u32;2])->[u32;2] {[m31_neg_ref(x[0]),m31_neg_ref(x[1])]}
pub fn qm31_neg_ref(x:[u32;4])->[u32;4] {[m31_neg_ref(x[0]),m31_neg_ref(x[1]),m31_neg_ref(x[2]),m31_neg_ref(x[3])]}
pub fn qm31_zero_ref(x:[u32;4])->bool { x[0]==0 && x[1]==0 && x[2]==0 && x[3]==0 }
pub fn bits_ref(eight:bool)->u32 {if eight {3}else{1}}
pub fn index_ref(x:&[u32;16],i:usize)->u32 {x[i]}
fn add_ref(x:u32,y:u32)->u32 {let s=x+y;if s>=2147483647{s-2147483647}else{s}}
pub fn prepared_ref(x:[u32;4])->[u32;9] {let a=add_ref(x[0],x[2]);let b=add_ref(x[1],x[3]);[x[0],x[1],add_ref(x[0],x[1]),x[2],x[3],add_ref(x[2],x[3]),a,b,add_ref(a,b)]}
