from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2e-20261023';P=E/'S2E-steps';(P/'src').mkdir(parents=True,exist_ok=True)
prior=R/'docs/research/100bit-spend-path-20261013/evidence/s2a-20261023/S2A-spec/S2A_Primitives.rs'
(P/'src/S2E_Trusted.rs').write_bytes(prior.read_bytes())
(P/'Cargo.toml').write_text('''[package]
name="s2e-steps"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
s2e-reference={path="../S2E-reference"}
solana-program="=2.3.0"
[profile.dev]
opt-level=3
debug=0
[profile.release]
opt-level=3
''')
(P/'src/lib.rs').write_text('''#![allow(dead_code,unexpected_cfgs)]
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
''')
(E/'S2E-step-domain.json').write_text(json.dumps({'trusted_spec_source':str(prior.relative_to(R)),'sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),'reused_contract':'s2a-20261023/kani-003: proof_for_contract(step), 1200 properties, zero failures','consumer_domain':'selected-cell counter/return projection; owned byte vectors empty (not a byte-frame proof); three cells/handles, three tokens, two payload coordinates, arbitrary signed counters, aliases allowed, Valid and Enabled required','source_shape_domain':'instruction slices length 0..4; arbitrary account_count usize','qualification':'SDK primitive projection and bounded pure source guard only; no full source-step simulation, child contract instantiation, metadata/allocator relation or E certificate.'},indent=2)+'\n')
