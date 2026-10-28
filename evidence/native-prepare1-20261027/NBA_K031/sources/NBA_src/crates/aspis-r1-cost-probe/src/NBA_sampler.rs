use super::*;
// Exactly ONE iteration of add_small_base_p on an arbitrary native pre-state.
fn NBA_add_digit(digit:&mut u32,addend:&mut u32){
 let sum=u64::from(*digit)+u64::from(*addend);
 *digit=(sum%u64::from(P)) as u32;
 *addend=(sum/u64::from(P)) as u32;
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_add_step(){
 let mut d:[u32;8]=unsafe{core::mem::transmute::<[u8;32],[u32;8]>(kani::any())};let old=d;let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<8&&j<8);let before:u32=kani::any();kani::assume(before<=257&&d[i]<P);let mut carry=before;let sum=u64::from(d[i])+u64::from(before);
 NBA_add_digit(&mut d[i],&mut carry);
 assert_eq!(carry,if sum>=u64::from(P){1}else{0});assert_eq!(u64::from(d[i]),if sum>=u64::from(P){sum-u64::from(P)}else{sum});assert!(d[i]<P);assert_eq!(d[j],if j==i{d[i]}else{old[j]});kani::cover!(carry==0,"no carry");kani::cover!(carry==1,"carry");
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_decode8(){
 let d:[u32;8]=unsafe{core::mem::transmute::<[u8;32],[u32;8]>(kani::any())};kani::assume(d[0]<P&&d[1]<P&&d[2]<P&&d[3]<P&&d[4]<P&&d[5]<P&&d[6]<P&&d[7]<P);let value=decode8(d);let j:usize=kani::any();kani::assume(j<8);assert_eq!(value.to_limbs()[j],d[j]);kani::cover!(true,"canonical digit packing");
}

static mut NBA_LPTR:*const u8=core::ptr::null();
static mut NBA_LD:[u32;8]=[0;8];static mut NBA_LQ:u32=0;static mut NBA_LS:usize=0;
fn NBA_can(d:&[u32;8])->bool{d[0]<P&&d[1]<P&&d[2]<P&&d[3]<P&&d[4]<P&&d[5]<P&&d[6]<P&&d[7]<P}
fn NBA_low_route(block:&[u8;32])->([u32;8],u32){unsafe{
 assert_eq!(NBA_LS,0);assert_eq!(block.as_ptr(),NBA_LPTR);NBA_LS=1;
 NBA_LD=core::mem::transmute::<[u8;32],[u32;8]>(kani::any());NBA_LQ=kani::any();kani::assume(NBA_can(&NBA_LD)&&NBA_LQ<=256);(NBA_LD,NBA_LQ)
}}
fn NBA_add_route(d:&mut[u32;8],a:u32)->bool{unsafe{
 let j:usize=kani::any();kani::assume(j<8);assert_eq!(d[j],NBA_LD[j]);assert!(NBA_can(d));assert!(a<=257);
 if NBA_LS==2{assert_eq!(a,1);kani::cover!(true,"wrapped gamma reaches second carry pass");kani::assume(false);}
 assert_eq!(NBA_LS,1);assert_eq!(a,NBA_LQ+1);NBA_LS=2;
 NBA_LD=core::mem::transmute::<[u8;32],[u32;8]>(kani::any());kani::assume(NBA_can(&NBA_LD));*d=NBA_LD;kani::any()
}}
fn NBA_decode_route(d:[u32;8])->WideExact{unsafe{
 let j:usize=kani::any();kani::assume(j<8);assert_eq!(d[j],NBA_LD[j]);assert!(NBA_can(&d));kani::cover!(true,"same canonical digits reach decoder");kani::assume(false);WideExact::ZERO
}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::sampler::low_base_p_digits,NBA_low_route)]
#[kani::stub(crate::sampler::add_small_base_p,NBA_add_route)]
#[kani::stub(crate::sampler::decode8,NBA_decode_route)]
fn NBA_sampler_routes(){let block:[u8;32]=kani::any();unsafe{NBA_LS=0;NBA_LPTR=block.as_ptr();if kani::any(){let _=gamma_sample(&block);}else{let _=ordinary_sample(&block);}}}

static mut NBA_QD:[u32;4]=[0;4];
fn NBA_qdigits(_block:&[u8;32])->[u32;4]{unsafe{NBA_QD=core::mem::transmute::<[u8;16],[u32;4]>(kani::any());kani::assume(NBA_QD[0]<P&&NBA_QD[1]<P&&NBA_QD[2]<P&&NBA_QD[3]<P);NBA_QD}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::sampler::qm31_digits,NBA_qdigits)]
fn NBA_qm31_pack(){let q=qm31_sample(&kani::any());let j:usize=kani::any();kani::assume(j<4);let out=[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];unsafe{assert_eq!(out[j],NBA_QD[j]);}kani::cover!(true,"four canonical digits packed into rho");}

// ONE frozen qm31_div_pass iteration, including the descending index update.
fn NBA_qdiv_iteration(rank:&mut[u32;8],remainder:&mut u64,j:&mut usize){
 *j-=1;
 let dividend=(*remainder<<32)|u64::from(rank[*j]);
 rank[*j]=(dividend/u64::from(P)) as u32;
 *remainder=dividend%u64::from(P);
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_qdiv_step(){
 let mut rank:[u32;8]=unsafe{core::mem::transmute::<[u8;32],[u32;8]>(kani::any())};let old=rank;let rem:u64=kani::any();let initial:usize=kani::any();let i:usize=kani::any();kani::assume(rem<u64::from(P)&&initial>0&&initial<=8&&i<8);let mut r=rem;let mut j=initial;NBA_qdiv_iteration(&mut rank,&mut r,&mut j);assert_eq!(j,initial-1);assert!(r<u64::from(P));let q=u64::from(rank[j]);let weighted=(q<<31)-q;assert_eq!(weighted+r,(rem<<32)|u64::from(old[j]));assert_eq!(rank[i],if i==j{rank[j]}else{old[i]});kani::cover!(true,"arbitrary descending rho division step");
}
static mut NBA_PASS_IN:[u32;8]=[0;8];static mut NBA_PASS_OUT:[u32;8]=[0;8];static mut NBA_PASS_REM:u32=0;static mut NBA_PASS_N:usize=0;
fn NBA_pass_route(rank:[u32;8])->([u32;8],u32){unsafe{
 let j:usize=kani::any();kani::assume(j<8);assert_eq!(rank[j],NBA_PASS_IN[j]);NBA_PASS_N+=1;NBA_PASS_OUT=core::mem::transmute::<[u8;32],[u32;8]>(kani::any());NBA_PASS_REM=kani::any();kani::assume(NBA_PASS_REM<P);(NBA_PASS_OUT,NBA_PASS_REM)
}}
fn NBA_qdigits_iteration(rank:&mut[u32;8],digits:&mut[u32;4],i:&mut usize){
 let (quotient,digit)=qm31_div_pass(*rank);
 *rank=quotient;
 digits[*i]=digit;
 *i+=1;
}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::sampler::qm31_div_pass,NBA_pass_route)]
fn NBA_qdigits_step(){
 let mut rank:[u32;8]=unsafe{core::mem::transmute::<[u8;32],[u32;8]>(kani::any())};let mut digits:[u32;4]=unsafe{core::mem::transmute::<[u8;16],[u32;4]>(kani::any())};let old=digits;let at:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(at<4&&j<8&&k<4);let mut i=at;unsafe{NBA_PASS_IN=rank;NBA_PASS_N=0;NBA_qdigits_iteration(&mut rank,&mut digits,&mut i);assert_eq!(NBA_PASS_N,1);assert_eq!(i,at+1);assert_eq!(rank[j],NBA_PASS_OUT[j]);assert_eq!(digits[k],if k==at{NBA_PASS_REM}else{old[k]});assert!(digits[at]<P);kani::cover!(true,"one rho digit callback and writeback");}
}
