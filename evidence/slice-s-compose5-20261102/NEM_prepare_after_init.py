from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative';subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True);assert 'let mut output = [0u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];' in f
body='''use super::*;
#[kani::proof]
fn after_init(){let output=[VALUE;POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];let j:usize=kani::any();kani::assume(j<688);assert!(output[j]==0,"same frozen zero initializer at arbitrary cell");}
'''.replace('VALUE','1u8' if negative else '0u8')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_after_init.rs"]\nmod NEM_after_init;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_after_init.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_AFTER_INIT_CURRENT.json').write_text(json.dumps(dict(negative=negative,source=p,one_arbitrary_cell=True,no_loop=True,classification='actual fixed-array scalar zero initializer; source length constant resolved by compiler'),indent=1)+'\n')
