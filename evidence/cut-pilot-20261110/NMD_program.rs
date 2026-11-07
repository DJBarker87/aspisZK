// Minimal ProgramResult Route B control. Its result domain is exactly
// Ok(()) or Custom(arg), established by this body, not every SDK error.
use super::*;
use solana_program::{entrypoint::ProgramResult,program_error::ProgramError};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NMD_model(before:[u64;4],arg:u32)->[u64;4]{[arg as u64,before[1].wrapping_add(1),before[2]^(arg as u64),before[3].rotate_left(1)]}
fn NMD_reply(ok:bool,arg:u32)->ProgramResult{if ok{Ok(())}else{Err(ProgramError::Custom(arg))}}
#[kani::modifies(state)]
#[kani::ensures(|out|*state==NMD_model(old(*state),arg)&&*out==NMD_reply(ok,arg))]
fn NMD_program_child(ok:bool,arg:u32,state:&mut[u64;4])->ProgramResult{
 state[0]=arg as u64;state[1]=state[1].wrapping_add(1);state[2]^=arg as u64;state[3]=state[3].rotate_left(1);NMD_reply(ok,arg)
}
#[kani::modifies(state)]
#[kani::ensures(|out|!(*state==NMD_model(old(*state),arg)&&*out==NMD_reply(ok,arg)))]
fn NMD_inverse_child(ok:bool,arg:u32,state:&mut[u64;4])->ProgramResult{NMD_program_child(ok,arg,state)}
fn NMD_construct_program_cut(ok:bool,arg:u32,state:&mut[u64;4])->ProgramResult{
 let before=*state;*state=kani::any();
 let out=if kani::any(){Ok(())}else{Err(ProgramError::Custom(kani::any()))};
 kani::assume(*state==NMD_model(before,arg));kani::assume(out==NMD_reply(ok,arg));out
}
fn NMD_construct_program_bad_reply(ok:bool,arg:u32,state:&mut[u64;4])->ProgramResult{let before=*state;*state=kani::any();kani::assume(*state==NMD_model(before,arg));NMD_reply(!ok,arg)}
fn NMD_construct_program_bad_state(ok:bool,arg:u32,state:&mut[u64;4])->ProgramResult{*state=kani::any();state[0]=arg as u64+1;NMD_reply(ok,arg)}
fn NMD_parent(){let before:[u64;4]=kani::any();let mut state=before;let ok:bool=kani::any();let arg:u32=kani::any();let out=NMD_program_child(ok,arg,&mut state);assert_eq!(out,NMD_reply(ok,arg));assert_eq!(state,NMD_model(before,arg));}
#[kani::proof_for_contract(NMD_program_child)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_program_contract(){let mut state:[u64;4]=kani::any();NMD_program_child(kani::any(),kani::any(),&mut state);}
#[kani::proof_for_contract(NMD_inverse_child)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_program_inverse(){let mut state:[u64;4]=kani::any();NMD_inverse_child(kani::any(),kani::any(),&mut state);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_program_real(){NMD_parent();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_program_child,NMD_construct_program_cut)]
fn NMD_program_cut(){NMD_parent();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_program_child,NMD_construct_program_bad_reply)]
fn NMD_program_bad_reply(){NMD_parent();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_program_child,NMD_construct_program_bad_state)]
fn NMD_program_bad_state(){NMD_parent();}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
