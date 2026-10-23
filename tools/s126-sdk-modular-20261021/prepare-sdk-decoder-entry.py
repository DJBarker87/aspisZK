#!/usr/bin/env python3
"""Pair actual frozen stage1 with the complete owned caller at decoder entry.
The decoder is the explicit cut and returns the same InvalidAccountData.
No verifier, encoder or post-verifier write may be reached in this check.
This is an entry-prefix correspondence, not whole stage1 refinement.
"""
from pathlib import Path
import json,hashlib,sys
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text();source=original
a=source.index('fn planned_decode(');b=source.index('fn planned_validate(',a)
source=source[:a]+'''fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 let phase=unsafe{PHASE.value};assert!(phase<2);
 let expected=if phase==0 {unsafe{NATIVE_ROOT_PTRS.value[1]}}else{unsafe{MODEL_ROOT_PTRS.value[1]}};
 assert_eq!(bytes.as_ptr(),expected);assert_eq!(bytes.len(),1880);
 unsafe{CALLS.value[phase][0]+=1;}
 Err(ProgramError::InvalidAccountData)
}
'''+source[b:]
source=source.replace('#[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]\n','').replace('#[kani::stub_verified(verified_byte_copy)]\n','')
source=source.replace('fn paired_parent_context()', 'fn paired_decoder_entry_context()')
source=source.replace(' let model=OwnedSdk{',''' let byte_offsets:[usize;3]=kani::any();
 kani::assume(byte_offsets[0]<58295);kani::assume(byte_offsets[1]<1880);kani::assume(byte_offsets[2]<1768);
 let initial_bytes=core::array::from_fn::<_,3,_>(|i|snapshots[i][byte_offsets[i]]);
 let model=OwnedSdk{''',1)
source=source.replace(' if actual.is_ok() {',' if unsafe{CALLS.value[0][0]}==1 {',1)
a=source.index('  assert!(expected.is_ok());');b=source.index('  for i in 0..3 {\n   assert_eq!(model.accounts',a)
source=source[:a]+'''  assert!(matches!(actual,Err(ProgramError::InvalidAccountData)));
  assert!(matches!(expected,Err(ProgramError::InvalidAccountData)));
  for phase in 0..2 {
   assert_eq!(unsafe{CALLS.value[phase][0]},1);
   for event in 1..4 {assert_eq!(unsafe{CALLS.value[phase][event]},0);}
  }
  for i in 0..3 {
   assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[i].add(byte_offsets[i]).read()},initial_bytes[i]);
   assert_eq!(model.data_cells[i].bytes[byte_offsets[i]],initial_bytes[i]);
  }
'''+source[b:]
source=source.replace('kani::cover!(actual.is_ok(),"paired parent accepts with full arbitrary checkpoint bytes");','kani::cover!(unsafe{CALLS.value[0][0]}==1,"native and complete owned caller reach identical decoder entry");')
source=source.replace('kani::cover!(actual.is_ok()&&matches!(plan().statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}),"withdrawal parent accepts");','kani::cover!(unsafe{CALLS.value[0][0]}==1&&initial_counts[0]==isize::MAX,"decoder entry does not yet acquire the proof buffer");')
prefix=original[:original.index('#[cfg(kani)] mod proofs')];assert source.startswith(prefix)
if len(sys.argv)>3 and sys.argv[3]=='descriptors':
 a=source.index(' let byte_offsets:');b=source.index(' let model=OwnedSdk{',a)
 source=source[:a]+source[b:]
 a=source.index('  for i in 0..3 {\n   assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[i].add(byte_offsets[i])')
 b=source.index('  for i in 0..3 {\n   assert_eq!(model.accounts',a)
 source=source[:a]+source[b:]
(out/'src/lib.rs').write_text(source);(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),base_source_sha256=sha(original),unchanged_source_prefix_sha256=sha(prefix),qualification=__doc__,domain='Complete real AccountInfo stage1 prefix and complete owned stage1, arbitrary metadata/signed borrow counters/independent lamport alias map and all bytes of three distinct rooted buffers of lengths58295/1880/1768. Native decoder entry implies corresponding owned decoder entry on its original public buffer, full error and SDK metadata/counters preserved, and one arbitrary queried byte in each entire buffer unchanged. The native scan is separately overapproximated; accepted-prefix scope and concrete scan/decoder installation remain explicit. No successful decode or later-stage join is inferred.'),indent=2)+'\n')
if len(sys.argv)>3 and sys.argv[3]=='descriptors':
 p=out/'source-cut.json';m=json.loads(p.read_text());m['domain']=m['domain'].replace(', and one arbitrary queried byte in each entire buffer unchanged','');m['retained_byte_frame']='This context checks exact decoder-entry pointer/length and complete account metadata/counter correspondence, not an arbitrary byte query. Native acquisition write frames and reference acquisition/read byte-frame theorems must be composed separately; no complete byte/runtime embedding is inferred.';p.write_text(json.dumps(m,indent=2)+'\n')
