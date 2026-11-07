use super::*;
#[path="PCF_AccountReference.rs"] mod reference;
fn exact(r:&ProgramResult,code:u32)->bool {
    match r {Ok(())=>code==0,Err(ProgramError::Custom(c))=>*c==code && code!=0,_=>false}
}
pub(super) fn payer_contract(p:&AccountInfo<'_>,s:&AccountInfo<'_>,r:&ProgramResult)->bool {
    let code=reference::payer_reference(p.is_signer,p.is_writable,p.executable,p.owner==&system_program::id(),
        s.key==&system_program::id(),s.owner==&native_loader::id(),s.executable,s.is_signer,s.is_writable);
    exact(r,code)
}
pub(super) fn token_contract(a:&AccountInfo<'_>,r:&ProgramResult)->bool {
    let code=reference::token_reference(a.key==&LEGACY_SPL_TOKEN_PROGRAM_ID,a.executable,a.is_signer,a.is_writable,
        a.owner==&bpf_loader::id(),a.owner==&bpf_loader_upgradeable::id(),a.owner==&loader_v4::id());
    exact(r,code)
}
#[cfg(kani)]
#[kani::proof_for_contract(require_payer_and_system_program)]
fn payer_contract_proof(){
    let pk=Pubkey::new_from_array(kani::any());let po=Pubkey::new_from_array(kani::any());
    let sk=Pubkey::new_from_array(kani::any());let so=Pubkey::new_from_array(kani::any());
    let mut pl:u64=kani::any();let mut sl:u64=kani::any();let mut pd=[];let mut sd=[];
    let p=AccountInfo::new(&pk,kani::any(),kani::any(),&mut pl,&mut pd,&po,kani::any(),kani::any());
    let s=AccountInfo::new(&sk,kani::any(),kani::any(),&mut sl,&mut sd,&so,kani::any(),kani::any());
    let _=require_payer_and_system_program(&p,&s);
}
#[cfg(kani)]
#[kani::proof_for_contract(require_token_program_account)]
fn token_contract_proof(){
    let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
    let mut lamports:u64=kani::any();let mut data=[];
    let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),kani::any());
    let _=require_token_program_account(&a);
}

#[cfg(kani)]
#[kani::proof_for_contract(require_payer_and_system_program)]
fn payer_alias_contract_proof(){
    let pk=Pubkey::new_from_array(kani::any());let po=Pubkey::new_from_array(kani::any());
    let sk=Pubkey::new_from_array(kani::any());let so=Pubkey::new_from_array(kani::any());
    let mut lamports:u64=kani::any();let mut data=[];
    let p=AccountInfo::new(&pk,kani::any(),kani::any(),&mut lamports,&mut data,&po,kani::any(),kani::any());
    let mut s=p.clone();s.key=&sk;s.owner=&so;s.is_signer=kani::any();s.is_writable=kani::any();s.executable=kani::any();s.rent_epoch=kani::any();
    let _=require_payer_and_system_program(&p,&s);
}

#[cfg(kani)]
#[kani::proof]
fn constants_proof(){
 assert_eq!((system_program::id()).to_bytes(),[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
 assert_eq!((native_loader::id()).to_bytes(),[5,135,132,191,20,139,164,40,47,176,18,87,72,136,169,241,83,160,125,173,247,101,192,69,92,154,151,3,128,0,0,0]);
 assert_eq!((bpf_loader::id()).to_bytes(),[2,168,246,145,78,136,161,110,57,90,225,40,148,143,250,105,86,147,55,104,24,221,71,67,82,33,243,198,0,0,0,0]);
 assert_eq!((bpf_loader_upgradeable::id()).to_bytes(),[2,168,246,145,78,136,161,176,226,16,21,62,247,99,174,43,0,194,185,61,22,193,36,210,192,83,122,16,4,128,0,0]);
 assert_eq!((loader_v4::id()).to_bytes(),[5,18,180,17,81,81,227,122,173,10,139,197,211,136,46,123,127,218,76,243,210,192,40,200,207,131,54,24,0,0,0,0]);
 assert_eq!((LEGACY_SPL_TOKEN_PROGRAM_ID).to_bytes(),[6,221,246,225,215,101,161,147,217,203,225,70,206,235,121,172,28,180,133,237,95,91,55,145,58,140,245,133,126,255,0,169]);
 #[cfg(PCF_NEG_IDS)] assert_ne!(system_program::id().to_bytes(),[0;32]);
}

#[cfg(kani)]
#[kani::modifies()]
#[kani::ensures(|r| matches!(r,Ok(())))]
fn empty_frame(a:&AccountInfo<'_>)->ProgramResult {let _=a.is_signer;Ok(())}
#[cfg(kani)]
#[kani::modifies()]
#[kani::ensures(|r| matches!(r,Ok(())))]
fn bad_frame(a:&AccountInfo<'_>)->ProgramResult {
 let mut value=a.lamports.borrow_mut();**value=(**value).wrapping_add(1);Ok(())
}
#[cfg(kani)]
#[kani::proof_for_contract(empty_frame)]
fn empty_frame_proof(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut data=[];
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),kani::any());
 let _=empty_frame(&a);
}
#[cfg(kani)]
#[kani::proof_for_contract(bad_frame)]
fn bad_frame_proof(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut data=[];
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),kani::any());
 let _=bad_frame(&a);
}

// Method calibration only: no PDA value is computed or assumed.
#[cfg(kani)]
extern "C" { fn __CPROVER_uninterpreted_PCF_u8(x:u8)->u8; }
#[cfg(kani)]
#[kani::proof]
fn pda_uf_repeat(){
 let x:u8=kani::any();let a=unsafe{__CPROVER_uninterpreted_PCF_u8(x)};
 let b=unsafe{__CPROVER_uninterpreted_PCF_u8(x)};assert_eq!(a,b);
}
#[cfg(kani)]
#[kani::proof]
fn pda_uf_unimplied(){
 let x:u8=kani::any();let y:u8=kani::any();kani::assume(x!=y);
 let a=unsafe{__CPROVER_uninterpreted_PCF_u8(x)};
 let b=unsafe{__CPROVER_uninterpreted_PCF_u8(y)};assert_eq!(a,b);
}
