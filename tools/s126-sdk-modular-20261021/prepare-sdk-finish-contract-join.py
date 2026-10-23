#!/usr/bin/env python3
"""Full native/owned post-child state comparison using the exact checked
all-reply-length frozen finish contract with a constant ghost destination.
Source normalization, outer child replies and caller/log transport remain open.
"""
from pathlib import Path
import sys,tempfile,subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);T=R/'tools/s126-sdk-modular-20261021'
subprocess.run(['python3',str(T/'prepare-sdk-finish-join.py'),str(O),'normalized'],check=True)
p=O/'src/lib.rs';s=p.read_text()
s=s.replace('let mut b1:[u8;58295]','let mut b1:[u8;1880]').replace('let mut b2:[u8;58295]','let mut b2:[u8;1768]')
def cut(text,name):
 a=text.index('fn '+name);i=text.index('{',a)+1;depth=1
 while depth:depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[a:i]
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(T/'prepare-sdk-finish-fixed-frame.py'),d,'all-reply-lengths','bool-outcome'],check=True)
 leaf=(Path(d)/'src/lib.rs').read_text()
 a=leaf.index('fn native_finish(');b=leaf.index('\n#[cfg(kani)] mod proofs',a);definition=leaf[a:b]
 a=leaf.index(' #[kani::proof_for_contract(encoded_finish)]');harness=leaf[a:leaf.rfind('\n}')]
s=s.replace(cut(s,'native_finish'),definition+'\n'+harness)
s=s.replace('trace:&mut Vec<[isize;3]>)->Result<(),ProgramError> {','trace:&mut Vec<[isize;3]>,observed:usize,destination:*mut [u8;1768],expected:u8)->Result<(),ProgramError> {',1)
s=s.replace(' let result=native_finish(&mut checkpoint_data,reply);',' let source=reply.as_ptr().cast::<[u8;1768]>();\n let outcome=encoded_finish(&mut checkpoint_data,&reply,observed,destination,source,expected);\n let result=if outcome {Ok(())}else{Err(ProgramError::InvalidAccountData)};\n drop(reply);')
s=s.replace('#[kani::proof] #[kani::unwind(40)]','#[kani::stub_verified(encoded_finish)]\n#[kani::proof] #[kani::unwind(40)]')
observation=' let observed_slot:usize=kani::any();kani::assume(observed_slot<3);\n let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);\n'
s=s.replace(' let mut expected_trace=Vec::new();',observation+' let copy_index=if observed_slot==2 {observed}else{0};\n let expected_byte=if reply_len==1768 {reply_bytes[copy_index]}else{model.data_cells[2].bytes[copy_index]};\n let mut expected_trace=Vec::new();')
s=s.replace('native_chain(&accounts,reply,&counters,&mut actual_trace)', 'native_chain(&accounts,reply,&counters,&mut actual_trace,copy_index,pointers[2] as *mut [u8;1768],expected_byte)')
s=s.replace(' let observed_slot:usize=kani::any();kani::assume(observed_slot<3);\n if lengths[observed_slot]>0 {\n  let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);',' if lengths[observed_slot]>0 {')
checkpointQuery=len(sys.argv)>2 and sys.argv[2]=='checkpoint-query'
if checkpointQuery:
 s=s.replace('let observed_slot:usize=kani::any();kani::assume(observed_slot<3);','let observed_slot=2usize;')
p.write_text(s)
c=O/'Cargo.toml';c.write_text(c.read_text().replace('aspis-s126-sdk-finish-join','aspis-s126-sdk-finish-contract-join'))
m=json.loads((O/'source-cut.json').read_text());sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
m.update(source_sha256=sha(s),qualification=__doc__,finish_leaf_source_sha256=sha(leaf),finish_definition_sha256=sha(definition),leaf_proof='sdk-finish-fixed-frame-join-v5',result_encoding='The checked concrete wrapper retains original full ProgramError and excludes every other variant by checked unreachable panic; parent reconstructs exact Ok or InvalidAccountData.',owner_drop='Borrowed reply helper; explicit drop(reply) occurs immediately after helper return and before proof/public/checkpoint guard destruction, preserving the original owned-helper drop order.',domain='Actual full SDK and full OwnedSdk, distinct58295/1880/1768 data nodes/all bytes, all metadata and signed counters, independent lamport aliases, real Rc headers. Every reply length0..1769 and all bytes. Complete status/acquisition trace/drop counters/Rc metadata and arbitrary byte in every root compared. Exact destination ghost pointer is the actual checkpoint root; all leaf preconditions must be checked. Earlier reached-entry normalization and source caller/child/log/heap-embedding transports remain open.')
(O/'source-cut.json').write_text(json.dumps(m,indent=2)+'\n')

if checkpointQuery:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['observation_scope']='Checkpoint value, complete return/acquisition trace/counters/metadata/lengths. Other data-node contents are not observed by this context; compose the separately checked native destination-only frame and owned record-update frame before claiming complete heap equality.'
 m['domain']=m['domain'].replace('arbitrary byte in every root compared','arbitrary checkpoint byte compared; other root-byte equality remains a frame-composition obligation')
 p.write_text(json.dumps(m,indent=2)+'\n')
