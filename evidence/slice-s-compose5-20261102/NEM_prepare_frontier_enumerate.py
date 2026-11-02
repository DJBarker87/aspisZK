from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative';subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
body='''use super::*;
use aspis_core::field::M31;
use crate::Digest;
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn frontier_enumerate(){let nodes=[NODES];let level:usize=kani::any();kani::assume(level<=20);let mut iter=nodes.iter().enumerate();if level>0{let _=iter.nth(level-1);}let next=iter.next();if level<20{let(count,node)=next.unwrap();assert!(count==COUNT && core::ptr::eq(node,&nodes[level]),"actual frontier Enumerate count and node");assert!(iter.len()==19-level);}else{assert!(next.is_none()&&iter.len()==0);}}
'''.replace('NODES',','.join(['digest()']*20)).replace('COUNT','level+1' if negative else 'level')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_frontier_enumerate.rs"]\nmod NEM_frontier_enumerate;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_frontier_enumerate.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_FRONTIER_ENUMERATE_CURRENT.json').write_text(json.dumps(dict(negative=negative,one_next=True,all_raw_frontiers=True,arbitrary_level_le20=True,no_output_allocation=True,classification='actual Enumerate cursor association, isolated from byte writes after NEL_K054 timeout'),indent=1)+'\n')
