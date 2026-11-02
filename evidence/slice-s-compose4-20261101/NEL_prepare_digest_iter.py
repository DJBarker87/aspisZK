from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/atomic_statement.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
body='''use super::*;
#[kani::proof]
fn iterator_step(){
 let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let index:usize=kani::any();kani::assume(index<=8);
 let mut iter=d[index..].iter();let next=iter.next();
 if index<8{assert!(core::ptr::eq(next.unwrap(),&d[index]),"same suffix iterator limb");assert!(iter.as_slice().len()==7-index);assert!(iter.as_slice().as_ptr()==d[index+1..].as_ptr());}
 else{assert!(next.is_none() && iter.as_slice().is_empty());}
}
'''
if negative:body=body.replace('next.unwrap(),&d[index]','next.unwrap(),&d[(index+1)%8]')
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_digest_iter.rs"]\nmod NEL_digest_iter;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/NEL_digest_iter.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_DIGEST_ITER_CURRENT.json').write_text(json.dumps(dict(negative=negative,domain='all arbitrary raw Digest, index <=8',iterator_prestate='actual native slice iterator constructed from arbitrary remaining suffix',same_place=True,exhausted_case=True,count_invariant='base count=index; next count=index+1; Lean DigestTotal.cursor and next_row',loop_induction='AspisR1.S2K.DigestBytes.loop_exact',not_whole_buffer=True),indent=1)+'\n')
