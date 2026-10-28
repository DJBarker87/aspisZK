use super::*;
const NBL_P:u32=aspis_core::field::P;
static mut NBL_D:[u32;4]=[0;4];
fn NBL_qdigits(_block:&[u8;32])->[u32;4]{unsafe{
 NBL_D=core::mem::transmute::<[u8;16],[u32;4]>(kani::any());kani::assume(NBL_D[0]<NBL_P&&NBL_D[1]<NBL_P&&NBL_D[2]<NBL_P&&NBL_D[3]<NBL_P);NBL_D
}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::sampler::qm31_digits,NBL_qdigits)]
fn NBL_rho_pack(){
 let block:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<4);
 let out=crate::sampler::qm31_sample(&block);let limbs=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0];
 unsafe{assert_eq!(limbs[i],NBL_D[i]);}kani::cover!(true,"rho preserves every returned canonical digit");
}
// ONE exact initialization iteration in qm31_digits; all other words framed.
fn NBL_init_step(block:&[u8;32],rank:&mut[u32;8],i:&mut usize){
 let start=4*(*i);
 rank[*i]=u32::from_le_bytes([block[start],block[start+1],block[start+2],block[start+3]]);
 *i+=1;
}
#[kani::proof] #[kani::unwind(3)]
fn NBL_rho_init(){
 let block:[u8;32]=kani::any();let mut rank:[u32;8]=unsafe{core::mem::transmute::<[u8;32],[u32;8]>(kani::any())};let old=rank;
 let j:usize=kani::any();let before:usize=kani::any();kani::assume(j<8&&before<8);let mut i=before;
 NBL_init_step(&block,&mut rank,&mut i);assert_eq!(i,before+1);
 let k=4*before;let value=u64::from(block[k])+256*u64::from(block[k+1])+65536*u64::from(block[k+2])+16777216*u64::from(block[k+3]);
 assert_eq!(u64::from(rank[before]),value);assert_eq!(rank[j],if j==before{rank[before]}else{old[j]});
 kani::cover!(true,"arbitrary byte-word initialization and complete rank frame");
}
