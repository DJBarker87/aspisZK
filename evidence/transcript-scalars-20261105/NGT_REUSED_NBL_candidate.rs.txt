use super::*;
static mut NBL_MODE:u8=0;
static mut NBL_STEP:usize=0;
static mut NBL_PTR:*const u8=core::ptr::null();
static mut NBL_DIGITS:[u32;8]=[0;8];
static mut NBL_Q:u32=0;
static mut NBL_OUT:E=E::ZERO;
fn NBL_canonical(d:&[u32;8])->bool {d[0]<aspis_core::field::P&&d[1]<aspis_core::field::P&&d[2]<aspis_core::field::P&&d[3]<aspis_core::field::P&&d[4]<aspis_core::field::P&&d[5]<aspis_core::field::P&&d[6]<aspis_core::field::P&&d[7]<aspis_core::field::P}
fn NBL_low(block:&[u8;32])->([u32;8],u32){unsafe{
 assert_eq!(NBL_STEP,0);assert_eq!(block.as_ptr(),NBL_PTR);NBL_STEP=1;
 NBL_DIGITS=core::mem::transmute::<[u8;32],[u32;8]>(kani::any());NBL_Q=kani::any();kani::assume(NBL_canonical(&NBL_DIGITS)&&NBL_Q<=256);(NBL_DIGITS,NBL_Q)
}}
fn NBL_add(d:&mut[u32;8],a:u32)->bool{unsafe{
 let i:usize=kani::any();kani::assume(i<8);assert_eq!(d[i],NBL_DIGITS[i]);assert!(NBL_canonical(d));
 let first=NBL_STEP==1;if first {assert_eq!(a,NBL_Q+1);}else{assert_eq!(NBL_STEP,2);assert_eq!(NBL_MODE,2);assert_eq!(a,1);}
 assert!(a<=257);NBL_STEP+=1;NBL_DIGITS=core::mem::transmute::<[u8;32],[u32;8]>(kani::any());kani::assume(NBL_canonical(&NBL_DIGITS));*d=NBL_DIGITS;
 // The false second carry is paired with NBL_SamplerDebug.source on the
 // SAME low/first/second traces, not with canonicality alone.
 first&&NBL_MODE==2
}}
fn NBL_decode(d:[u32;8])->E{unsafe{
 assert_eq!(NBL_STEP,if NBL_MODE==0{1}else if NBL_MODE==1{2}else{3});
 let i:usize=kani::any();kani::assume(i<8);assert_eq!(d[i],NBL_DIGITS[i]);assert!(NBL_canonical(&d));NBL_STEP+=1;
 NBL_OUT=core::mem::transmute::<[u8;32],E>(kani::any());NBL_OUT
}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::sampler::low_base_p_digits,NBL_low)]
#[kani::stub(crate::sampler::add_small_base_p,NBL_add)]
#[kani::stub(crate::sampler::decode8,NBL_decode)]
fn NBL_sampler_return(){
 let mode:u8=kani::any();let i:usize=kani::any();kani::assume(mode<3&&i<8);let block:[u8;32]=kani::any();unsafe{NBL_MODE=mode;NBL_STEP=0;NBL_PTR=block.as_ptr();}
 let out=if mode==0{crate::sampler::ordinary_sample(&block)}else{crate::sampler::gamma_sample(&block)};
 unsafe{assert_eq!(NBL_STEP,if mode==0{2}else if mode==1{3}else{4});assert_eq!(out.to_limbs()[i],NBL_OUT.to_limbs()[i]);}
 kani::cover!(mode==0,"ordinary return");kani::cover!(mode==1,"unwrapped gamma return");kani::cover!(mode==2,"wrapped gamma returns after paired zero second carry");
}
