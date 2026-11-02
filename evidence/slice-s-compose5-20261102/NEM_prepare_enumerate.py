"""One actual Enumerate::next from an arbitrary reachable suffix/count."""
from pathlib import Path
import subprocess,difflib,json,hashlib,sys
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/atomic_statement.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=f.index('pub fn encode_digest_canonical(');z=f.index('\n}',a)+2;source=f[a:z]
assert 'digest.iter().enumerate()' in source
body='''use super::*;
#[kani::proof]
fn enumerate_step(){
 let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let index:usize=kani::any();kani::assume(index<=8);
 let mut iter=d.iter().enumerate();
 // nth is constant-time on the native slice iterator: no whole-buffer loop.
 if index>0 {let _=iter.nth(index-1);}
 let before=iter.len();let next=iter.next();
 if index<8{let (count,value)=next.unwrap();assert!(count==COUNT,"exact native Enumerate count");assert!(core::ptr::eq(value,&d[index]),"same actual M31 place");assert!(before==8-index && iter.len()==7-index,"exact remaining suffix lengths");}
 else{assert!(before==0 && next.is_none() && iter.len()==0,"exhausted iterator");}
}
'''.replace('COUNT','index+1' if negative else 'index')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_enumerate.rs"]\nmod NEM_enumerate;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/NEM_enumerate.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_ENUMERATE_CURRENT.json').write_text(json.dumps(dict(negative=negative,source=p,frozen_body=source,frozen_body_sha256=hashlib.sha256(source.encode()).hexdigest(),domain='every raw Digest; arbitrary index <= 8',prestate='native Enumerate over actual digest, positioned by constant-time slice nth; count=index and suffix=d[index..]',one_next=True,not_whole_buffer=True,child='actual M31 place at actual count; closed serializer receives it',classification='rule B: native iterator state/count association; emitted association separate'),indent=1)+'\n')
