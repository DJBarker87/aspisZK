"""Actual u8 std fill intrinsic, one indexed observation and outside guards.
The pinned specialization is a write_bytes primitive, not a protocol loop.
"""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','late'];N=800 if case=='live' else 1520
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True);assert f.count('output.fill(0);')>=2
body='''#[kani::proof]
fn fill_intrinsic(){let mut output:[u8;SIZE]=kani::any();let j:usize=kani::any();kani::assume(j<SIZE);let old=output[j];let out=&mut output[1..END];out.fill(VALUE);assert!(output[j]==if j>=1&&j<END{0}else{old},"actual std u8 fill with complete allocation frame");}
'''.replace('SIZE',str(N+2)).replace('END',str(N+1)).replace('VALUE','1' if negative else '0')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_fill.rs"]\nmod NEM_fill;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_fill.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_FILL_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,length=N,source=p,actual_std_fill=True,observation='arbitrary index over complete allocation with both outside guard cells',classification='native primitive u8 SpecFill specialization calls write_bytes; no Rust/protocol loop is unrolled',new_copy_stub=False),indent=1)+'\n')
