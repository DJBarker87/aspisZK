"""One protocol-loop iteration and one pinned copy iteration, full prestate."""
from pathlib import Path
import subprocess,difflib,json,sys,hashlib
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/atomic_statement.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
start=frozen.index('pub fn encode_digest_canonical(');end=frozen.index('\n}',start)+2
assert 'bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());' in frozen[start:end]
expected='if j==index*4+offset{frame.reply[offset]}else{old}'
if negative:expected='('+expected+')^1'
body='''#![allow(non_snake_case)]
use super::*;
struct Frame{expected:M31,reply:[u8;4],called:bool}
fn serialize(value:&M31,frame:&mut Frame)->[u8;4]{assert!(value.0==frame.expected.0 && !frame.called,"same native limb at serialization call");frame.called=true;frame.reply}
#[kani::requires(index<8 && offset<4 && j<32 && old==bytes[j] && !frame.called && frame.expected.0==digest[index].0)]
#[kani::modifies(bytes,&mut frame.called)]
#[kani::ensures(|r| *r==offset+1 && frame.called && bytes[j]==EXPECTED)]
fn step(bytes:&mut[u8;32],digest:&Digest,index:usize,offset:usize,j:usize,old:u8,frame:&mut Frame)->usize{
 let value=&digest[index];let reply=serialize(value,frame);
 let dst=&mut bytes[index*4..index*4+4];let src=&reply;let mut i=offset;
 dst[i]=src[i];i+=1;i
}
#[kani::proof_for_contract(step)]
fn digest_step(){let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut bytes:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<8);let offset:usize=kani::any();kani::assume(offset<4);let j:usize=kani::any();kani::assume(j<32);let old=bytes[j];let mut frame=Frame{expected:d[index],reply:kani::any(),called:false};step(&mut bytes,&d,index,offset,j,old,&mut frame);}
'''.replace('EXPECTED',expected)
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_digest_step.rs"]\nmod NEL_digest_step;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/NEL_digest_step.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_DIGEST_STEP_CURRENT.json').write_text(json.dumps(dict(source=path,frozen_body_sha256=hashlib.sha256(frozen[start:end].encode()).hexdigest(),negative=negative,one_native_protocol_iteration=True,one_KMX_copy_iteration=True,arbitrary_prestate=True,local_argument_log=True,child_domain='all raw M31; serializer requires no canonical precondition',composition='NEJ_WindowStep.iteration; NED_DigestCohorts.digest_encode; NEJ serializer contract; actual iter/enumerate step association still separately required'),indent=1)+'\n')
