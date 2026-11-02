"""Join actual Enumerate next and one copy iteration on the same prestate."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/atomic_statement.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=f.index('pub fn encode_digest_canonical(');z=f.index('\n}',a)+2;original=f[a:z]
assert 'bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());' in original
body='''use super::*;
struct Frame{reply:[u8;4],called:bool}
fn serialize(v:&M31,expected:&M31,f:&mut Frame)->[u8;4]{assert!(!f.called && core::ptr::eq(v,expected),"same-call actual iterator word");f.called=true;f.reply}
#[kani::proof]
fn digest_call(){
 let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let cursor:usize=kani::any();kani::assume(cursor<8);let offset:usize=kani::any();kani::assume(offset<4);let j:usize=kani::any();kani::assume(j<32);
 let mut bytes:[u8;32]=kani::any();let old=bytes[j];let mut f=Frame{reply:kani::any(),called:false};
 let mut iter=d.iter().enumerate();if cursor>0{let _=iter.nth(cursor-1);}
 let (index,value)=iter.next().unwrap();let reply=serialize(value,&d[EXPECTED],&mut f);
 // Exactly the KMX copy value iteration for this actual native window.
 let dst=&mut bytes[index*4..index*4+4];let mut i=offset;dst[i]=reply[i];i+=1;
 assert!(index==cursor && f.called && i==offset+1 && iter.len()==7-cursor,"native next, call, and copy cursor");
 assert!(bytes[j]==if j==cursor*4+offset{f.reply[offset]}else{old},"same prestate indexed byte and full external frame");
}
'''.replace('EXPECTED','(cursor+1)%8' if negative else 'cursor')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_digest_call.rs"]\nmod NEM_digest_call;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/NEM_digest_call.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_DIGEST_CALL_CURRENT.json').write_text(json.dumps(dict(negative=negative,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),rule='B',arbitrary_prestate=True,actual_enumerate_count=True,same_borrow_place=True,unconstrained_fixed4_reply=True,modifies='local called flag and single actual output cell',classification='one iterator/serializer/copy value iteration; KMX loop induction and emitted association required'),indent=1)+'\n')
