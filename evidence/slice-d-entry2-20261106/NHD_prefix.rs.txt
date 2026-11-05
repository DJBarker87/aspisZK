//! Rejection prefixes only, local old-state frames; accepted suffixes remain open.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn make()->core::mem::ManuallyDrop<[OwnedAccount;8]>{core::mem::ManuallyDrop::new(core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Err(ProgramError::AccountBorrowFailed),bytes:Err(ProgramError::AccountBorrowFailed)}))}

#[kani::requires(a.len()!=7)]
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn auth_count_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{let r=core::mem::ManuallyDrop::new(authenticate_asq8_accounts(v,a,p,0,slot));if a.len()<7{matches!(&*r,Err(ProgramError::NotEnoughAccountKeys))}else{matches!(&*r,Err(ProgramError::InvalidArgument))}}
#[kani::proof_for_contract(auth_count_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_count(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=7);let _=auth_count_packet(&v,&p,&accounts[..n],kani::any());}

#[kani::requires(a.len()!=7)]
#[kani::ensures(|r| !*r)]
#[kani::modifies()]
fn auth_count_wrong_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{let r=core::mem::ManuallyDrop::new(authenticate_asq8_accounts(v,a,p,0,slot));if a.len()<7{matches!(&*r,Err(ProgramError::NotEnoughAccountKeys))}else{matches!(&*r,Err(ProgramError::InvalidArgument))}}
#[kani::proof_for_contract(auth_count_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_count_wrong(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=7);let _=auth_count_wrong_packet(&v,&p,&accounts[..n],kani::any());}

#[kani::requires(a.len()!=3)]
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn stage1_count_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{let r=core::mem::ManuallyDrop::new(stage1_owned(v,a,&[3,10]));matches!(&*r,Err(ProgramError::InvalidInstructionData))}
#[kani::proof_for_contract(stage1_count_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=3);let _=stage1_count_packet(&v,&p,&accounts[..n],kani::any());}

#[kani::requires(a.len()!=3)]
#[kani::ensures(|r| !*r)]
#[kani::modifies()]
fn stage1_count_wrong_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{let r=core::mem::ManuallyDrop::new(stage1_owned(v,a,&[3,10]));matches!(&*r,Err(ProgramError::InvalidInstructionData))}
#[kani::proof_for_contract(stage1_count_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count_wrong(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=3);let _=stage1_count_wrong_packet(&v,&p,&accounts[..n],kani::any());}

#[kani::requires(a.len()!=7)]
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn stage2_count_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{matches!(stage2_owned(v,a,b"ASQ8",Ok(slot)),Err(ProgramError::InvalidInstructionData))}
#[kani::proof_for_contract(stage2_count_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=7);let _=stage2_count_packet(&v,&p,&accounts[..n],kani::any());}

#[kani::requires(a.len()!=7)]
#[kani::ensures(|r| !*r)]
#[kani::modifies()]
fn stage2_count_wrong_packet(v:&Pubkey,p:&Pubkey,a:&[OwnedAccount],slot:u64)->bool{matches!(stage2_owned(v,a,b"ASQ8",Ok(slot)),Err(ProgramError::InvalidInstructionData))}
#[kani::proof_for_contract(stage2_count_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count_wrong(){let accounts=make();let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let n:usize=kani::any();kani::assume(n<=8&&n!=7);let _=stage2_count_wrong_packet(&v,&p,&accounts[..n],kani::any());}
