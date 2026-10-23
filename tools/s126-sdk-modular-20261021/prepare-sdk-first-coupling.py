#!/usr/bin/env python3
"""Pair native and complete borrowed reference through the first/verifier call.
The common successful first reply is empty, so no checkpoint write is reached.
Native bytes/SDK write frame must be checked, not assumed. Three actual-carrier
SDK models have independent direct native/model coupling and unary frame checks;
their source/ABI/domain and contextual substitution remain explicit boundaries.
"""
from pathlib import Path
import hashlib,json,runpy,sys
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
out=Path(sys.argv[1]);assert not out.exists();(out/'src').mkdir(parents=True)
base=(E/'sdk-native-frame-windows/sources/sdk-shared-prefix-v19/src/lib.rs').read_text()
old=(E/'sdk-parent-cuts/sources/sdk-native-context-v9/src/lib.rs').read_text()
prefix=base[:base.index('#[cfg(kani)] mod proofs')]
hooks=old[old.index('#[derive(Clone,Copy)] struct Plan'):old.index('#[kani::stub(crate::error,unreachable_error)]')]
hooks=hooks.replace('statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],output:[u8;1769],output_len:usize,k:usize','statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],k:usize')
hooks=hooks.replace('if phase==0 {unsafe{NATIVE_ROOT_PTRS.value[1]}}else{unsafe{PUBLIC_SNAPSHOT_PTR.value}}','unsafe{NATIVE_ROOT_PTRS.value[1]}')
hooks=hooks.replace('if phase==0{unsafe{NATIVE_ROOT_PTRS.value[1]}}else{unsafe{PUBLIC_SNAPSHOT_PTR.value}}','unsafe{NATIVE_ROOT_PTRS.value[1]}')
hooks=hooks.replace('if phase==0{unsafe{NATIVE_ROOT_PTRS.value[0]}}else{unsafe{PROOF_SNAPSHOT_PTR.value}}','unsafe{NATIVE_ROOT_PTRS.value[0]}')
hooks=hooks.replace('Ok(plan().output[..plan().output_len].to_vec())','Ok(Vec::new())')
hooks=hooks.replace('let phase=unsafe{PHASE.value};assert!(phase<2);\n let expected=', 'let phase=unsafe{PHASE.value};assert!(phase<2);assert_eq!(unsafe{CALLS.value[phase]},[0,0,0,0]);\n let expected=',1)
hooks=hooks.replace('let phase=unsafe{PHASE.value};assert_eq!(statement as *const _','let phase=unsafe{PHASE.value};assert_eq!(unsafe{CALLS.value[phase]},[1,0,0,0]);assert_eq!(statement as *const _')
hooks=hooks.replace('let phase=unsafe{PHASE.value};assert_eq!(afterstate as *const _','let phase=unsafe{PHASE.value};assert_eq!(unsafe{CALLS.value[phase]},[1,1,0,0]);assert_eq!(afterstate as *const _')
hooks=hooks.replace('let phase=unsafe{PHASE.value};assert!(phase<2);assert!(observer.is_none());','let phase=unsafe{PHASE.value};assert!(phase<2);assert_eq!(unsafe{CALLS.value[phase]},[1,1,1,0]);assert!(observer.is_none());')
hooks+='''
fn planned_scan(_: &[u8])->bool{false}
fn unreachable_copy<T:Copy>(_:&mut[T],_:&[T]){panic!("empty first reply must reject before checkpoint copy")}
'''
start=base.index('fn native_prefix(');tail=base[start:]
tail=tail.replace('#[kani::proof] #[kani::unwind(48)]','#[kani::proof_for_contract(native_prefix)] #[kani::unwind(700)]',1)
a=tail.index('#[kani::stub(');b=tail.index('fn native_owned_decoder_prefix()',a)
tail=tail[:a]+'''#[kani::stub(AccountInfo::try_data_len,crate::sdk_live_models::Models::length)]
#[kani::stub(AccountInfo::try_borrow_data,crate::sdk_live_models::Models::shared)]
#[kani::stub(AccountInfo::try_borrow_mut_data,crate::sdk_live_models::Models::exclusive)]
#[kani::stub(crate::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,planned_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,planned_encode)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx1,planned_tx1)]
#[kani::stub(crate::error,unreachable_error)]
#[kani::stub(<[u8]>::copy_from_slice,unreachable_copy)]
'''+tail[b:]
needle=' unsafe{PUBLIC_PTR.value=pointers[1];HITS.value=[0;2];PHASE.value=0;}'
assert tail.count(needle)==1
tail=tail.replace(needle,''' unsafe{NATIVE_ROOT_PTRS.value=pointers;CALLS.value=[[0;4];2];PHASE.value=0;
 PLAN.value=Some(Plan{statement:statement(),candidate:kani::any(),k:instruction[1] as usize});}
''')
tail=tail.replace('unsafe{HITS.value[0]}==1','unsafe{CALLS.value[0][0]}==1')
tail=tail.replace('assert!(matches!(&actual,Err(ProgramError::InvalidAccountData)));','assert!(matches!(&actual,Err(ProgramError::InvalidAccountData)|Err(ProgramError::AccountBorrowFailed)));')
needle='assert!(matches!((&actual,&expected),(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))),"native reached decoder implies same complete reference decoder/error");'
assert tail.count(needle)==1
tail=tail.replace(needle,'''assert!(matches!((&actual,&expected),
   (Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))|
   (Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))),
   "native and complete reference return the same exact first-prefix error");''')
tail=tail.replace('assert_eq!(unsafe{HITS.value},[1,1]);','assert_eq!(unsafe{CALLS.value[0]},unsafe{CALLS.value[1]},"native/reference child prefix, counts and order coincide");')
tail=tail.replace('unsafe{HITS.value}==[1,1]','unsafe{CALLS.value[0]}==[1,1,1,1]&&unsafe{CALLS.value[1]}==[1,1,1,1]')
tail=tail.replace('&&initial_counts[0]==isize::MAX','&&initial_counts[0]==isize::MAX-1')
tail=tail.replace('native and complete borrowed reference reach the same original decoder bytes','native and complete reference reach the same original first-call bytes')
tail=tail.replace('decoder entry before proof acquisition supports saturated proof borrow','first entry supports maximum permitted shared-borrow count')
tail=tail.replace('native decoder entry implies same complete reference decoder/error','native first-prefix implies matching complete reference')
assert 'HITS.' not in tail and 'PUBLIC_PTR.' not in tail
frame='''#[kani::modifies(unsafe{COUNTERS.value[0].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[1].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[2].cast_mut().cast::<isize>()},
 unsafe{core::ptr::addr_of_mut!(CALLS.value)},
 unsafe{core::ptr::addr_of_mut!(BOX_PTRS.value)},
 unsafe{core::ptr::addr_of_mut!(CANDIDATE_PTRS.value)},
 unsafe{core::ptr::addr_of_mut!(PUBLIC_KIND.value)},
 unsafe{core::ptr::addr_of_mut!(PUBLIC_PARTS.value)})]
'''
s=prefix+'''mod sdk_live_models;
#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk_borrowed as owned;
use owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};
use std::cell::Cell;
struct GhostStorage<T>{value:T,allocation_tag:u64}
static mut COUNTERS:GhostStorage<[*const Cell<isize>;3]>=GhostStorage{value:[core::ptr::null();3],allocation_tag:0x51a4000000000001};
'''+hooks+frame+tail
(out/'src/lib.rs').write_text(s)
model=(R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs').read_text()
model=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated'](model)
(out/'src/sdk_live_models.rs').write_text(model)
c=(E/'sdk-native-frame-windows/sources/sdk-shared-prefix-v19/Cargo.toml').read_text().replace('name="aspis-s126-sdk-shared-prefix-pair-separated-frame"','name="aspis-s126-sdk-shared-prefix-first-coupling-v1"')
(out/'Cargo.toml').write_text(c)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(out/'src/lib.rs'),model_sha256=sha(out/'src/sdk_live_models.rs'),base_source_sha256=hashlib.sha256(base.encode()).hexdigest(),native_source_prefix_sha256=hashlib.sha256(prefix[:-1].encode()).hexdigest(),qualification=__doc__,domain='All original fixed-length proof/public/checkpoint allocations, metadata, instruction/account counts0..3, independent arbitrary data/lamport aliases, signed counters and nonzero Rc fields. Unseeded proof/candidate independent. Both complete native/reference first wrappers execute; common typed successful child replies, first reply empty. Parent native frame must be enforced before original buffers are reused. No initialization/image assumption.',remaining='Actual source scan and installed child substitution, full successful first-output/writeback continuation and arbitrary runtime heap/ABI/oracle transport. Ordinary SDK model contextual substitution consumes the direct coupling plus unary frames, not just codegen. No full native/S2 closure.'),indent=2)+'\n')
