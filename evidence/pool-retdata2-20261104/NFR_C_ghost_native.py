"""Actual helper local-log exploration. Instrumented allocation domain only."""
from pathlib import Path
import subprocess,json,difflib,sys
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata-20261104';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1];assert mode in ['direct','direct-byte','direct-error','direct-field','direct-call','direct-pointer','direct-length','direct-frame','direct-variant']
original=json.loads((O/'NFO_K007-shape.json').read_text())['source']
helpers=original[original.index('fn digest()'):original.index('struct Runtime {')]
source='use super::*;\nuse aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\n'+helpers+r'''
struct Frame{calls:u8,expected:*const PoolV1PairForestTerminalResultV1,family:u8,row:usize,word:usize,index:usize,field:u64,ok:bool,reply:[u8;792]}
#[repr(C)]
struct Input{value:PoolV1PairForestTerminalResultV1,frame:core::cell::UnsafeCell<Frame>}
fn encode_stub(value:&PoolV1PairForestTerminalResultV1)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>{
 // DIAGNOSTIC DOMAIN: value is the first field of the harness's local Input.
 // No production Box<Result> carrier law follows from this layout assumption.
 let input=value as *const PoolV1PairForestTerminalResultV1 as *const Input;
 let f=unsafe{&mut *(*input).frame.get()};
 assert!(f.calls==0&&core::ptr::eq(value,f.expected));
 assert!(observe(value,f.family,f.row,f.word,f.index)==f.field);
 f.calls=1;
 if f.ok{Ok(f.reply)}else{Err(any_error())}
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_result_v1,encode_stub)]
fn association(){
 let family:u8=kani::any();kani::assume(family<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let index:usize=kani::any();kani::assume(index<32);
 let value=result();let field=observe(&value,family,row,word,index);
 let reply:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);let byte=reply[j];let ok:bool=kani::any();
 let input=Input{value,frame:core::cell::UnsafeCell::new(Frame{calls:0,expected:core::ptr::null(),family,row,word,index,field,ok,reply})};
 let ptr=&input.value as *const PoolV1PairForestTerminalResultV1;
 unsafe{(*input.frame.get()).expected=ptr;}
 let answer=terminal_result_bytes_box_v1(&input.value);
 let f=unsafe{&*input.frame.get()};
 assert!(f.calls==1);
 if ok{let out=answer.unwrap();assert!(out.len()==792&&out[j]==byte);}
 else{assert!(matches!(answer,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnData.into()));}
 assert!(observe(&input.value,family,row,word,index)==field);
}
'''
if mode=='direct-byte':source=source.replace('out[j]==byte','out[j]==(byte^1)')
if mode=='direct-error':source=source.replace('e==PoolV1ProgramError::InvalidVerifierReturnData.into()','e==ProgramError::InvalidArgument')
if mode=='direct-field':source=source.replace('==f.field);','==(f.field^1));')
if mode=='direct-call':source=source.replace('f.calls==1);','f.calls==2);')
if mode=='direct-pointer':source=source.replace('&&core::ptr::eq(value,f.expected)','&&!core::ptr::eq(value,f.expected)')
if mode=='direct-length':source=source.replace('out.len()==792','out.len()==791')
if mode=='direct-frame':source=source.replace('==field);','==(field^1));')
if mode=='direct-variant':source=source.replace('let answer=terminal_result_bytes_box_v1(&input.value);','let answer=terminal_result_bytes_box_v1(&input.value);assert!(answer.is_ok()!=ok);')
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFR_CDirect.rs"]\nmod NFR_CDirect;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFR_CDirect.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFR_C_native.patch').write_text(patch)
(E/'NFR_C_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification='DIAGNOSTIC: ACTUAL frozen terminal_result_bytes_box_v1 with full arbitrary encoder Results and LOCAL UnsafeCell log. Geometry requires argument first field of repr(C) Input; not production Box geometry, no enclosing caller credit without erasure',harness='pair_forest::NFR_CDirect::association'),indent=1)+'\n')
