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
