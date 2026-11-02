"""K054 replacement: isolate iteration from byte updates; no unchanged retry."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;part,mode=sys.argv[1:];negative=mode=='negative';assert part in ['iterator','cell']
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
if part=='iterator':
 body='''use super::*;
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn frontier_step(){let nodes=[NODES];let level:usize=kani::any();kani::assume(level<=20);let mut iter=nodes[level..].iter();let next=iter.next();if level<20{let observed=OBSERVED;assert!(core::ptr::eq(observed,&nodes[level]),"same frontier iterator place");assert!(iter.as_slice().len()==19-level && iter.as_slice().as_ptr()==nodes[level+1..].as_ptr());assert!(level+1<=20);}else{assert!(next.is_none()&&iter.as_slice().is_empty());}}
'''.replace('NODES',','.join(['digest()']*20)).replace('OBSERVED','&nodes[(level+1)%20]' if negative else 'next.unwrap()')
else:
 body='''#[kani::proof]
fn frontier_step(){let mut out:[u8;32]=kani::any();let start:usize=kani::any();let width:usize=kani::any();kani::assume(start<=32 && width<=32-start && width>0);let offset:usize=kani::any();kani::assume(offset<width);let j:usize=kani::any();kani::assume(j<32);let old=out[j];let value:u8=kani::any();let dst=&mut out[start..start+width];let src=&[value];let mut i=offset;dst[i]=src[0];i+=1;assert!(i==offset+1);assert!(out[j]==if j==start+offset{value}else{old});}
'''
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_frontier_step.rs"]\nmod NEL_frontier_step;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_frontier_step.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_FRONTIER_SPLIT_CURRENT.json').write_text(json.dumps(dict(part=part,negative=negative,replaces='NEL_K054 TIMEOUT; iterator and output are no longer coupled',original_harness_name_retained=True,one_iteration=True,no_function_contract=True,scope='native arbitrary suffix iterator' if part=='iterator' else 'native dynamic window and arbitrary byte update; 32-byte digest buffer, no outer loop'),indent=1)+'\n')
