use super::*;
pub(super) static mut RAW:[u64;3]=[0;3];
pub(super) static mut FACTORS:[(u64,u64);3]=[(0,0);3];
pub(super) fn product(n:usize,a:u64,b:u64)->u64{unsafe{FACTORS[n]=(a,b);RAW[n]}}
#[cfg(NDN_interpolation_factors)]
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn interpolation_factors(){
 let w:[u32;3]=kani::any();let c:[u32;3]=kani::any();unsafe{RAW=[0;3];}
 let _=super::interpolate_three_constant_limb(w[0],w[1],w[2],c[0],c[1],c[2]);
 let good=unsafe{FACTORS[0]==(u64::from(w[0]),u64::from(c[0]))&&FACTORS[1]==(u64::from(w[1]),u64::from(c[1]))&&FACTORS[2]==(u64::from(w[2]),u64::from(c[2]))};
 assert!(good!=cfg!(NDN_invert));
}
#[cfg(NDN_interpolation_sum)]
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn interpolation_sum(){
 let r:[u64;3]=kani::any();for x in r {kani::assume(x<=2147483646u64*2147483646u64);}
 unsafe{RAW=r;}
 let out=super::interpolate_three_constant_limb(0,0,0,0,0,0);
 let expected=super::NDE_native::reference::reduce_ref(r[0]+r[1]+r[2]);
 assert!((out.0==expected)!=cfg!(NDN_invert));
}
