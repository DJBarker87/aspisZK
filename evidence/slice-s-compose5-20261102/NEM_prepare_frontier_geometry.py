"""Split the timed-out iterator/write shape: only physical window geometry."""
from pathlib import Path
import sys,subprocess,json,difflib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','after'];N=800 if case=='live' else 688;base=160 if case=='live' else 48
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile' if case=='live' else 'pair_terminal';p='crates/aspis-statement/src/pool_v1/'+file+'.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True);assert f'let start = {base} + 32 * level;' in f
body=f'''#[kani::proof]
fn frontier_geometry(){{let mut output:[u8;{N}]=kani::any();let level:usize=kani::any();kani::assume(level<20);let offset:usize=kani::any();kani::assume(offset<32);let original=output.as_mut_ptr();let start={base}+32*level;let dst=&mut output[start..start+32];assert!(dst.len()==32);assert!(dst.as_mut_ptr().wrapping_add(offset)==original.wrapping_add({base}+32*level+offset{'+1' if negative else ''}),"same actual frontier child output place");}}
'''
changed=f+'\n#[cfg(kani)]\n#[path="NEM_frontier_geometry.rs"]\nmod NEM_frontier_geometry;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_frontier_geometry.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_FRONTIER_GEOMETRY_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,base=base,length=N,one_arbitrary_level=True,one_arbitrary_offset=True,no_byte_update=True,replaces='NEL_K054 coupled iterator/write timeout: separate count, typed window provenance, and small 32-byte update laws'),indent=1)+'\n')
