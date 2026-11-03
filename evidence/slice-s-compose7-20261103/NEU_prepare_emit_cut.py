"""Split K005/K007 into four-byte guard and untouched borrowed-slice send."""
from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;shape,mode=sys.argv[1:];assert shape in ['header','send'];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);a=f.index('fn emit_result(');z=f.index('\n}',a)+2;original=f[a:z]
if shape=='header':
 body='''use super::*;
fn guard(length:usize,header:&[u8;4])->ProgramResult{if length!=POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES||header[..]!=POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC{return Err(ProgramError::InvalidInstructionData)}Ok(())}
#[kani::proof]
fn emission_cut(){let h:[u8;4]=kani::any();let length:usize=kani::any();let good=length==792&&h[0]==65&&h[1]==83&&h[2]==82&&h[3]==56;assert!(guard(length,&h)==if good{Ok(())}else{Err(ProgramError::InvalidInstructionData)});}
'''
 if mode=='negative':body=body.replace('h[2]==82','h[2]==83')
else:
 body='''use super::*;
struct Frame{ptr:*const u8,length:usize,calls:u8}
fn output(bytes:&[u8],frame:&mut Frame){assert!(core::ptr::eq(bytes.as_ptr(),frame.ptr));assert!(bytes.len()==frame.length);frame.calls+=1;}
fn send(encoded:&[u8;792],frame:&mut Frame)->ProgramResult{output(&encoded[@START@..],frame);Ok(())}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEU_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEU_KMX::KMX_copy_from_slice)]
fn emission_cut(){let encoded:[u8;792]=kani::any();let mut f=Frame{ptr:encoded.as_ptr(),length:792,calls:0};let actual=send(&encoded,&mut f);assert!(actual==Ok(())&&f.calls==1);}
'''.replace('@START@','1' if mode=='negative' else '0')
changed=f+'\n#[cfg(kani)]\n#[path="NEU_emit_cut.rs"]\nmod NEU_emit_cut;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/programs/r1-cost-probe/src/NEU_emit_cut.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())
p2='programs/r1-cost-probe/src/lib.rs';f2=subprocess.check_output(['git','show','4bb3b3f5:'+p2],text=True);c2='#![cfg_attr(kani, feature(allocator_api))]\n'+f2+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NEU_KMX;\n';patch+=''.join(difflib.unified_diff(f2.splitlines(True),c2.splitlines(True),fromfile='a/'+p2,tofile='b/'+p2));(E/'NEU_native_contracts.patch').write_text(patch)
(E/'NEU_EMIT_CUT_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,frozen_body=original,domain='all usize lengths and four-byte headers' if shape=='header' else 'every typed borrowed792-byte encoded buffer',classification='separate actual suffix guard and runtime argument carrier; no runtime syscall value or op53 instance'),indent=1)+'\n')
