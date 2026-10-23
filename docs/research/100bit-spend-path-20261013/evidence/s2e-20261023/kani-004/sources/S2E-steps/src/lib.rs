#![allow(dead_code,unexpected_cfgs)]
#![cfg(kani)]
#[path="S2E_Trusted.rs"] mod sdk;
use s2e_reference::S2E_Reference::*;
use solana_program::program_error::ProgramError;

fn account(s: &sdk::State,a: usize) -> OwnedAccount {
 OwnedAccount { key:kani::any(),owner:kani::any(),is_signer:kani::any(),
 is_writable:kani::any(),executable:kani::any(),rent_epoch:kani::any(),
 data_slot:s.accounts[a],lamports_slot:s.lamports[a] as usize }
}
fn cell(s: &sdk::State,c: usize) -> OwnedDataCell {
 OwnedDataCell { bytes:Vec::new(),
 borrowed:s.counter[c] as isize,strong:kani::any(),weak:kani::any() }
}
fn lamports() -> OwnedLamportsCell {
 OwnedLamportsCell {amount:kani::any(),borrowed:kani::any(),strong:kani::any(),weak:kani::any()}
}
fn owned(s: &sdk::State) -> OwnedSdk {
 OwnedSdk {accounts:vec![account(s,0),account(s,1),account(s,2)],
 data_cells:vec![cell(s,0),cell(s,1),cell(s,2)],
 lamports_cells:vec![lamports(),lamports(),lamports()]}
}
// One library-substituted source step. This finite model does not assert typed
// Rust/SBF representation; the adopted fifteen fields license the library port.
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn shared_admitted_cut() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));
 let a:usize=kani::any();kani::assume(a<3);
 let op=sdk::Op::Shared{account:a,token:0,owner:100};kani::assume(sdk::enabled(&s,op));
 let mut o=owned(&s);let slot=o.accounts[a].data_slot;
 kani::assume(s.counter[slot]>=0 && s.counter[slot]<i64::MAX);
 let (post,reply)=sdk::step(s,op);
 let result=owned_acquire_shared(&mut o,slot);
 match reply {sdk::Reply::Guard(0)=>assert!(result.is_ok()),
 sdk::Reply::BorrowFailed=>assert_eq!(result,Err(ProgramError::AccountBorrowFailed)),_=>assert!(false)}
 assert_eq!(o.data_cells[slot].borrowed,post.counter[slot] as isize);
}
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn exclusive_cut() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));
 let a:usize=kani::any();kani::assume(a<3);
 let op=sdk::Op::Exclusive{account:a,token:0,owner:100};kani::assume(sdk::enabled(&s,op));
 let mut o=owned(&s);let slot=o.accounts[a].data_slot;
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 let (post,reply)=sdk::step(s,op);
 let result=owned_acquire_checkpoint(&mut o,&mut guards,slot);
 match reply {sdk::Reply::Guard(0)=>{assert!(result.is_ok());assert_eq!(guards.checkpoint,Some(slot));},
 sdk::Reply::BorrowFailed=>{assert_eq!(result,Err(ProgramError::AccountBorrowFailed));assert!(guards.checkpoint.is_none());},_=>assert!(false)}
 assert_eq!(o.data_cells[slot].borrowed,post.counter[slot] as isize);
}
#[kani::proof] #[kani::unwind(5)] #[kani::stub_verified(sdk::step)]
fn shared_rejected_cut() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));
 let a:usize=kani::any();kani::assume(a<3);
 let op=sdk::Op::Shared{account:a,token:0,owner:100};kani::assume(sdk::enabled(&s,op));
 let mut o=owned(&s);let slot=o.accounts[a].data_slot;
 kani::assume(s.counter[slot]<0 || s.counter[slot]==i64::MAX);
 let (post,reply)=sdk::step(s,op);
 let result=owned_acquire_shared(&mut o,slot);
 assert_eq!(reply,sdk::Reply::BorrowFailed);
 assert_eq!(result,Err(ProgramError::AccountBorrowFailed));
 assert_eq!(o.data_cells[slot].borrowed,post.counter[slot] as isize);
}
// Verbatim source guard, with only accounts.len() abstracted by its cut value.
fn native_shape1(data: &[u8],account_count: usize)->Result<(),ProgramError> {
 if !(data == &[3, 10] || data == &[3, 11]) || account_count != 3 {
  return Err(ProgramError::InvalidInstructionData);
 }
 Ok(())
}
#[kani::proof] #[kani::unwind(6)]
fn shape1_cut() {
 let data:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let count:usize=kani::any();
 assert_eq!(native_shape1(&data[..n],count),shape1(&data[..n],count));
}
