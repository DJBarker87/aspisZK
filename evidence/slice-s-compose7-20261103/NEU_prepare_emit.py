"""Split NEQ_K081: construction only, or suffix only; never retry the joined shape."""
from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose6-20261102'
shape,mode=sys.argv[1:];assert shape in ['construction','suffix','suffix_borrow'];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
a=f.index('fn emit_result(');z=f.index('\n}',a)+2;original=f[a:z]
patch=(P/'NEQ_K081-NEQ_native_contracts.patch').read_text();part=patch.split('+++ b/programs/r1-cost-probe/src/NEQ_emit.rs\n',1)[1].split('--- a/',1)[0];old='\n'.join(l[1:] for l in part.splitlines() if l.startswith('+'))+'\n'
helpers=old[:old.index('struct Frame')]
if shape=='construction':
 native=original[:original.index('    validate_pool')].replace('fn emit_result(statement: &PoolV1PairForestTerminalStatementV1) -> ProgramResult','fn construction(statement: &PoolV1PairForestTerminalStatementV1) -> PoolV1PairForestTerminalResultV1')+'    result\n}\n'
 body=helpers+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEU_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEU_KMX::KMX_copy_from_slice)]
fn construction_slice(){let s=NEE_statement();let r=construction(&s);let i:usize=kani::any();kani::assume(i<8);let j:usize=kani::any();kani::assume(j<32);let k:usize=kani::any();kani::assume(k<20);
 assert!(r.transition_kind==s.transition_kind());assert!(r.master_account[j]==s.common().master_account[j]);assert!(r.selected_lane_account[j]==s.common().selected_lane_account[j]);assert!(r.output_lane==s.common().output_lane);
 assert!(r.nullifier[i].0==s.nullifier()[i].0 @BAD@);let a=s.common().lane_transition.candidate_afterstate;assert!(r.verified_afterstate.next_pair_index==a.next_pair_index);assert!(r.verified_afterstate.next_root[i].0==a.next_root[i].0);assert!(r.verified_afterstate.next_frontier[k][i].0==a.next_frontier[k][i].0);}
'''.replace('@BAD@','^1' if mode=='negative' else '')
else:
 native=original[original.index('    if encoded.len()'):].replace('program::set_return_data(&encoded)','output(&encoded,f)')
 native='fn suffix(encoded:[u8;792],f:&mut Frame)->ProgramResult{\n'+native
 body='use super::*;\nstruct Frame{ptr:*const u8,j:usize,before:u8,out:u8,calls:u8}\nfn output(bytes:&[u8],f:&mut Frame){assert!(bytes.len()==792);f.ptr=bytes.as_ptr();f.out=bytes[f.j];f.calls+=1;}\n'+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEU_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEU_KMX::KMX_copy_from_slice)]
fn suffix_slice(){let encoded:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);let before:u8=kani::any();let mut f=Frame{ptr:core::ptr::null(),j,before,out:before,calls:0};let valid=encoded[0]==b'P'&&encoded[1]==b'F'&&encoded[2]==b'R'&&encoded[3]==b'1';let r=suffix(encoded,&mut f);assert!(r==if valid{Ok(())}else{Err(ProgramError::InvalidInstructionData)});assert!(f.calls==if valid{1}else{0});assert!(f.out==if valid{encoded[j] @BAD@}else{before});}
'''.replace('@BAD@','^1' if mode=='negative' else '')
if shape=='suffix_borrow':
 native=native.replace('encoded:[u8;792]','encoded:&[u8;792]')
 body='use super::*;\nstruct Frame{ptr:*const u8,calls:u8}\nfn output(bytes:&[u8],f:&mut Frame){assert!(bytes.len()==792);assert!(core::ptr::eq(bytes.as_ptr(),f.ptr));f.calls+=1;}\n'+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEU_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEU_KMX::KMX_copy_from_slice)]
fn suffix_slice(){let encoded:[u8;792]=kani::any();let mut f=Frame{ptr:encoded[@OFFSET@..].as_ptr(),calls:0};let valid=encoded[0]==b'P'&&encoded[1]==b'F'&&encoded[2]==b'R'&&encoded[3]==b'1';let r=suffix(&encoded,&mut f);assert!(r==if valid{Ok(())}else{Err(ProgramError::InvalidInstructionData)});assert!(f.calls==if valid{1}else{0});}
'''.replace('@OFFSET@','1' if mode=='negative' else '0')
# Derive magic from actual constant, not an invented fixture.
if shape in ['suffix','suffix_borrow']:
 stmt=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'],text=True)
 import re
 magic=re.search(r'POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[^=]*=\s*\*b"([^"]+)"',stmt).group(1)
 body=body.replace("b'P'&&encoded[1]==b'F'&&encoded[2]==b'R'&&encoded[3]==b'1'",'&&'.join('' if False else [])) if False else body
 body=body.replace("encoded[0]==b'P'&&encoded[1]==b'F'&&encoded[2]==b'R'&&encoded[3]==b'1'",'&&'.join(f'encoded[{i}]=={v}' for i,v in enumerate(magic.encode())))
changed=f+'\n#[cfg(kani)]\n#[path="NEU_emit.rs"]\nmod NEU_emit;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/programs/r1-cost-probe/src/NEU_emit.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())
p2='programs/r1-cost-probe/src/lib.rs';f2=subprocess.check_output(['git','show','4bb3b3f5:'+p2],text=True);c2='#![cfg_attr(kani, feature(allocator_api))]\n'+f2+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NEU_KMX;\n';patch+=''.join(difflib.unified_diff(f2.splitlines(True),c2.splitlines(True),fromfile='a/'+p2,tofile='b/'+p2));(E/'NEU_native_contracts.patch').write_text(patch)
(E/'NEU_EMIT_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),native=native,domain='every typed Statement' if shape=='construction' else 'every 792 byte array and arbitrary observation index',property='exact full constructed fields' if shape=='construction' else 'exact result, rejected frame and one runtime request byte; no claim of coherent op53 instance',classification='split native source projection with KMX and matched control; full emitter remains OPEN'),indent=1)+'\n')
