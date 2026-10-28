// Interface fidelity controls. No function pointers or Option<fn>.
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn verdict(v:bool)->bool{if cfg!(NDD_negative_controls){!v}else{v}}
#[kani::ensures(|r| verdict((*r & 1)==(x & 1)))]
fn scalar_weak(x:u32)->u32{x}
#[kani::proof_for_contract(scalar_weak)] fn scalar_proof(){scalar_weak(kani::any());}
#[kani::proof] fn scalar_real(){let x:u32=kani::any();assert_eq!(scalar_weak(x),x);}
#[kani::proof] #[kani::stub_verified(scalar_weak)] fn scalar_unimplied(){let x:u32=kani::any();assert_eq!(scalar_weak(x),x);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| *r==0)]
fn scalar_badframe(x:&mut[u32;2])->u32{x[1]=x[1].wrapping_add(1);0}
#[kani::proof_for_contract(scalar_badframe)] fn scalar_frame(){let mut x:[u32;2]=kani::any();scalar_badframe(&mut x);}

#[kani::ensures(|r| verdict(r[0]==x[0]))]
fn array32_weak(x:[u8;32])->[u8;32]{x}
#[kani::proof_for_contract(array32_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array32_proof(){array32_weak(kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array32_real(){let x:[u8;32]=kani::any();assert_eq!(array32_weak(x)[31],x[31]);}
#[kani::proof] #[kani::stub_verified(array32_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array32_unimplied(){let x:[u8;32]=kani::any();assert_eq!(array32_weak(x)[31],x[31]);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r[0]==0)]
fn array32_badframe(x:&mut[u8;32])->[u8;32]{x[31]=x[31].wrapping_add(1);[0;32]}
#[kani::proof_for_contract(array32_badframe)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array32_frame(){let mut x:[u8;32]=kani::any();array32_badframe(&mut x);}

#[kani::ensures(|r| verdict(r[0][0]==x[0][0]))]
fn nested9_weak(x:[[u32;3];3])->[[u32;3];3]{x}
#[kani::proof_for_contract(nested9_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn nested9_proof(){nested9_weak(kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn nested9_real(){let x:[[u32;3];3]=kani::any();assert_eq!(nested9_weak(x)[2][2],x[2][2]);}
#[kani::proof] #[kani::stub_verified(nested9_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn nested9_unimplied(){let x:[[u32;3];3]=kani::any();assert_eq!(nested9_weak(x)[2][2],x[2][2]);}
#[kani::modifies(&mut x[0][0])] #[kani::ensures(|r| r[0][0]==0)]
fn nested9_badframe(x:&mut[[u32;3];3])->[[u32;3];3]{x[2][2]=x[2][2].wrapping_add(1);[[0;3];3]}
#[kani::proof_for_contract(nested9_badframe)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn nested9_frame(){let mut x:[[u32;3];3]=kani::any();nested9_badframe(&mut x);}
