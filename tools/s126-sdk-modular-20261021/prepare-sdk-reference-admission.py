#!/usr/bin/env python3
"""Construct the complete borrowed reference from native-derived entry facts.
This target is conditional on those already checked scalar facts and the same
scan result. It does not execute or replace the SDK, or prove cut transport.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-frame-windows'
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=False)
base=(E/'sources/sdk-shared-prefix-v19/src/lib.rs').read_text()
native=base[:base.index('#[cfg(kani)] mod proofs')]
s=native+r'''#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk_borrowed as owned;
use owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};
static mut HITS:u8=0;
static mut PUBLIC_PTR:*const u8=core::ptr::null();
fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 assert_eq!(bytes.len(),1880,"reference reaches decoder on original public length");
 assert_eq!(bytes.as_ptr(),unsafe{PUBLIC_PTR},"reference reaches decoder on original public allocation");
 unsafe{HITS+=1;}
 Err(ProgramError::InvalidAccountData)
}
fn planned_scan(_: &[u8])->bool{false}
fn unreachable_first(_:Public<'_>,_:&[u8],_:&[u8],_:usize)->Result<Vec<u8>,ProgramError>{panic!("decoder-error prefix cannot reach first")}
fn unreachable_validate(_:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{panic!("decoder-error prefix cannot reach validator")}
fn unreachable_encode(_:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{panic!("decoder-error prefix cannot reach encoder")}
#[kani::proof] #[kani::unwind(48)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::first_decoded,unreachable_first)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,unreachable_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,unreachable_encode)]
fn reference_admission(){
 let program:[u8;32]=kani::any();let keys:[[u8;32];3]=kani::any();
 let owners:[[u8;32];3]=kani::any();let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let split:u8=kani::any();kani::assume(split==10 || split==11);
 kani::assume(keys[0]!=keys[1] && keys[0]!=keys[2] && keys[1]!=keys[2]);
 kani::assume(!flags[0][0] && !flags[0][1] && !flags[0][2]);
 kani::assume(!flags[1][0] && !flags[1][1] && !flags[1][2]);
 kani::assume(owners[2]==program && !flags[2][0] && flags[2][1] && !flags[2][2]);
 let buffers=[kani::vec::exact_vec::<u8,58295>(),kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let proof_slot:usize=kani::any();kani::assume(proof_slot<3);let data_slots=[proof_slot,1,2];
 let lamport_slots:[usize;3]=kani::any();for i in 0..3{kani::assume(lamport_slots[i]<3);}
 let counts:[isize;3]=kani::any();kani::assume(counts[2]==0);kani::assume(counts[1]>=0 && counts[1]<isize::MAX);
 let lamport_counts:[isize;3]=kani::any();let rc:[[usize;4];3]=kani::any();
 for i in 0..3{for j in 0..4{kani::assume(rc[i][j]>=1);}}
 let amounts:[u64;3]=kani::any();unsafe{HITS=0;PUBLIC_PTR=pointers[1];}
 let model=OwnedSdk{
  accounts:(0..3).map(|i|OwnedAccount{key:keys[i],owner:owners[i],is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:data_slots[i],lamports_slot:lamport_slots[i]}).collect(),
  data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:counts[i],strong:rc[i][0],weak:rc[i][1]-1}).collect(),
  lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:amounts[i],borrowed:lamport_counts[i],strong:rc[i][2],weak:rc[i][3]-1}).collect(),
 };
 let (result,out)=owned::owned_stage1(program,model,vec![3,split]);
 assert!(matches!(result,Err(ProgramError::InvalidAccountData)),"reference has the exact decoder-cut error");
 assert_eq!(unsafe{HITS},1,"reference reaches decoder exactly once from derived admission facts");
 for i in 0..3{
  assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);
  assert_eq!(out.data_cells[i].borrowed,counts[i]);
  assert_eq!(out.data_cells[i].strong,rc[i][0]);assert_eq!(out.data_cells[i].weak,rc[i][1]-1);
  assert_eq!(out.lamports_cells[i].amount,amounts[i]);assert_eq!(out.lamports_cells[i].borrowed,lamport_counts[i]);
  assert_eq!(out.lamports_cells[i].strong,rc[i][2]);assert_eq!(out.lamports_cells[i].weak,rc[i][3]-1);
 }
 kani::cover!(unsafe{HITS}==1 && counts[0]==isize::MAX,"reference prefix permits saturated proof counter");
 kani::cover!(unsafe{HITS}==1 && proof_slot==2,"reference prefix permits proof/checkpoint alias before proof acquisition");
}
}
'''
(O/'src/lib.rs').write_text(s)
c=(E/'sources/sdk-shared-prefix-v19/Cargo.toml').read_text().replace('name="aspis-s126-sdk-shared-prefix-pair-separated-frame"','name="aspis-s126-sdk-reference-admission"')
assert 'name="aspis-s126-sdk-reference-admission"' in c
(O/'Cargo.toml').write_text(c)
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),base_source_sha256=hashlib.sha256(base.encode()).hexdigest(),qualification=__doc__,input_facts='Exactly the scalar consequences of sdk-native-entry-facts-v1, with native-derived account/instruction lengths materialized as3/2. Original buffers reused after independent native frame, proof slot remains arbitrary0..2; independent lamport aliases/counters and Rc headers retained.',remaining='Same-scan transport, initial-buffer/native frame composition and decoder-cut continuation substitution remain explicit. Reference admission alone is not actual native/source equivalence or S2 closure.'),indent=2)+'\n')
