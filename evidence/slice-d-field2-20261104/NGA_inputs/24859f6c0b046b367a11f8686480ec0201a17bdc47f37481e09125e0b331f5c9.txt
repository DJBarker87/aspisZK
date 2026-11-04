use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
fn word(v:QM31,i:usize)->u32{match i{0=>v.c0.a.0,1=>v.c0.b.0,2=>v.c1.a.0,_=>v.c1.b.0}}
fn reference(v:[QM31;4],n:usize)->[u64;4]{let v0=if n>0{v[0]}else{QM31::ZERO};let v1=if n>1{v[1]}else{QM31::ZERO};let v2=if n>2{v[2]}else{QM31::ZERO};let v3=if n>3{v[3]}else{QM31::ZERO};let p=P as u64;
 let a=v0.c0.a.0 as u64+(p-v1.c0.b.0 as u64)+2*v2.c1.a.0 as u64+(p-v2.c1.b.0 as u64)+(p-v3.c1.a.0 as u64)+(2*p-2*v3.c1.b.0 as u64);
 let b=v0.c0.b.0 as u64+v1.c0.a.0 as u64+v2.c1.a.0 as u64+2*v2.c1.b.0 as u64+2*v3.c1.a.0 as u64+(p-v3.c1.b.0 as u64);
 let c=v0.c1.a.0 as u64+(p-v1.c1.b.0 as u64)+v2.c0.a.0 as u64+(p-v3.c0.b.0 as u64);
 let d=v0.c1.b.0 as u64+v1.c1.a.0 as u64+v2.c0.b.0 as u64+v3.c0.a.0 as u64;[a,b,c,d]}
fn checked<const LIMB:usize>(){let v=[any_q(),any_q(),any_q(),any_q()];for k in 0..4{kani::assume(canonical(v[k]));}let n:usize=kani::any();kani::assume(n<=4);let want=(reference(v,n)[LIMB]%(P as u64))as u32;let got=qm31_pack_base4(&v[..n]);assert!(word(got,LIMB)==if cfg!(NFT_invert){want^1}else{want});}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn pack0(){checked::<0>();}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn pack1(){checked::<1>();}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn pack2(){checked::<2>();}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn pack3(){checked::<3>();}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn copy4_positive(){let src=[any_q(),any_q(),any_q(),any_q()];let mut dst=[QM31::ZERO;4];unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<4&&j<4);assert!(word(src[i],j)==word(dst[i],j));}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)]
fn copy4_negative(){let src=[any_q(),any_q(),any_q(),any_q()];let mut dst=[QM31::ZERO;4];unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<4&&j<4);assert!(word(src[i],j)!=word(dst[i],j));}
