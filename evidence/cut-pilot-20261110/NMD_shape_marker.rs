use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::modifies(frame)]#[kani::ensures(|_out|true)]
fn NMD_shape(frame:&mut u8){*frame=7;}
#[kani::modifies(frame)]#[kani::ensures(|_out|false)]
fn NMD_inverse_shape(frame:&mut u8){*frame=7;}
#[kani::modifies(frame)]#[kani::ensures(|_out|true)]
fn NMD_modifies_shape(frame:&mut u8,other:&mut u8){*frame=7;*other=1;}
#[kani::proof_for_contract(NMD_shape)]
fn NMD_contract(){let mut frame:u8=kani::any();NMD_shape(&mut frame);}
#[kani::proof_for_contract(NMD_inverse_shape)]
fn NMD_inverse(){let mut frame:u8=kani::any();NMD_inverse_shape(&mut frame);}
#[kani::proof]
fn NMD_real(){let mut frame:u8=kani::any();NMD_shape(&mut frame);assert_eq!(frame,7);}
#[kani::proof]#[kani::stub_verified(NMD_shape)]
fn NMD_unimplied(){let mut frame:u8=kani::any();NMD_shape(&mut frame);assert_eq!(frame,7);}
#[kani::proof_for_contract(NMD_modifies_shape)]
fn NMD_modifies(){let mut frame:u8=kani::any();let mut other=0;NMD_modifies_shape(&mut frame,&mut other);}
