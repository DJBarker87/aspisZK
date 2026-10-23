#!/usr/bin/env python3
"""Complete borrowed-reference successful first path from native-derived facts.
Conditional reference construction, not a replacement for actual native SDK.
Admitted prefix/tag initializer requires existing gate/image transport. All
children return shared typed successful replies. Source installation remains.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
T=R/'tools/s126-sdk-modular-20261021'
subprocess.run(['python3',str(T/'prepare-sdk-first-coupling.py'),str(O)],check=True)
p=O/'src/lib.rs';base=p.read_text();a=base.index('#[cfg(kani)] mod proofs');b=base.index('#[kani::modifies(',a)
prefix=base[:a].replace('mod sdk_live_models;\n','');hooks=base[a:b]
hooks=hooks.replace('statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],k:usize','statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],output:[u8;1768],k:usize')
hooks=hooks.replace('Ok(Vec::new())','Ok(plan().output.to_vec())')
start=base.index('fn statement()->');end=base.index('fn native_prefix(',start) if 'fn native_prefix(' in base[start:] else -1
# The typed statement generator precedes the native wrapper in the original hooks.
assert 'fn statement()' in hooks
h=r'''
#[kani::proof] #[kani::unwind(700)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,planned_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,planned_encode)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx1,planned_tx1)]
fn reference_first(){
 let program:[u8;32]=kani::any();let keys:[[u8;32];3]=kani::any();let owners:[[u8;32];3]=kani::any();
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();let split:u8=kani::any();
 kani::assume(split==10 || split==11);kani::assume(keys[0]!=keys[1]&&keys[0]!=keys[2]&&keys[1]!=keys[2]);
 kani::assume(!flags[0][0]&&!flags[0][1]&&!flags[0][2]);kani::assume(!flags[1][0]&&!flags[1][1]&&!flags[1][2]);
 kani::assume(owners[2]==program&&!flags[2][0]&&flags[2][1]&&!flags[2][2]);
 let candidate:[u8;688]=kani::any();let output:[u8;1768]=kani::any();
 let mut proof=kani::vec::exact_vec::<u8,58295>();proof[..688].copy_from_slice(&candidate);proof[696]=2;
 let buffers=[proof,kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let counts:[isize;3]=kani::any();kani::assume(counts[2]==0);
 for i in 0..2{kani::assume(counts[i]>=0 && counts[i]<isize::MAX);}
 let lamport_slots:[usize;3]=kani::any();for i in 0..3{kani::assume(lamport_slots[i]<3);}
 let lamport_counts:[isize;3]=kani::any();let rc:[[usize;4];3]=kani::any();for i in 0..3{for j in 0..4{kani::assume(rc[i][j]>=1);}}
 let amounts:[u64;3]=kani::any();let index:usize=kani::any();kani::assume(index<1768);
 unsafe{NATIVE_ROOT_PTRS.value=pointers;CALLS.value=[[0;4];2];PHASE.value=0;PLAN.value=Some(Plan{statement:statement(),candidate,output,k:split as usize});}
 let model=OwnedSdk{
 accounts:(0..3).map(|i|OwnedAccount{key:keys[i],owner:owners[i],is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:i,lamports_slot:lamport_slots[i]}).collect(),
 data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:counts[i],strong:rc[i][0],weak:rc[i][1]-1}).collect(),
 lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:amounts[i],borrowed:lamport_counts[i],strong:rc[i][2],weak:rc[i][3]-1}).collect()};
 let(result,out)=owned::owned_stage1(program,model,vec![3,split]);
 assert!(result.is_ok(),"native-derived first facts construct successful complete borrowed reference");
 assert_eq!(unsafe{CALLS.value[0]},[1,1,1,1]);assert_eq!(out.data_cells[2].bytes[index],output[index]);
 for i in 0..3{
 assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);assert_eq!(out.data_cells[i].borrowed,counts[i]);
 assert_eq!(out.data_cells[i].strong,rc[i][0]);assert_eq!(out.data_cells[i].weak,rc[i][1]-1);
 assert_eq!(out.lamports_cells[i].amount,amounts[i]);assert_eq!(out.lamports_cells[i].borrowed,lamport_counts[i]);
 assert_eq!(out.lamports_cells[i].strong,rc[i][2]);assert_eq!(out.lamports_cells[i].weak,rc[i][3]-1);}
 kani::cover!(result.is_ok()&&counts[0]==isize::MAX-1,"successful reference with maximum permitted proof count");
 kani::cover!(result.is_ok()&&split==11,"successful reference split11");
}
}
'''
s=prefix+hooks+h;p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-shared-prefix-first-coupling-v1','aspis-s126-sdk-reference-first-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Native entry/frame certificate instantiation, source gate/image/scan transport, pure typed child installed source correctness and actual returned checkpoint writer/reader/runtime/oracle correspondence remain. This is a conditional successful reference constructor, not whole S2.'),indent=2)+'\n')
