"""Controls for usize result with mutable fixed-array output, local state only."""
from pathlib import Path
import subprocess,difflib,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1]
assert mode in ['native','unimplied','contract','inverted','frame']
subprocess.run([sys.executable,str(E/'NEJ_prepare_step.py'),'0','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
expr='*r != offset+1' if mode=='inverted' else '*r == offset+1'
frame='&mut out[..2]' if mode=='frame' else 'out'
body=f'''#![allow(non_snake_case)]
#[kani::requires(offset<4)]
#[kani::modifies({frame})]
#[kani::ensures(|r| {expr})]
fn weak(out:&mut [u8;216],offset:usize)->usize{{out[offset]=42;offset+1}}
'''
if mode in ['contract','inverted','frame']:
 body+='''#[kani::proof_for_contract(weak)]
fn common_window(){let mut out:[u8;216]=kani::any();let offset:usize=kani::any();kani::assume(offset<4);let _=weak(&mut out,offset);}
'''
else:
 body+='#[kani::proof_for_contract(weak)]\nfn contract_support(){let mut out:[u8;216]=kani::any();let offset:usize=kani::any();kani::assume(offset<4);let _=weak(&mut out,offset);}\n'
 body+='#[kani::proof]\n'+('#[kani::stub_verified(weak)]\n' if mode=='unimplied' else '')+'''fn common_window(){let mut out:[u8;216]=kani::any();let old=out[4];let offset:usize=kani::any();kani::assume(offset<4);let r=weak(&mut out,offset);assert!(r==offset+1);assert!(out[4]==old,"NEJ unimplied output frame");}
'''
changed=frozen+'\n#[cfg(kani)]\n#[path="NEJ_common_window.rs"]\nmod NEJ_common_window;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEJ_common_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEJ_native_contracts.patch').write_text(patch)
(E/'NEJ_SHAPE_CURRENT.json').write_text(json.dumps(dict(mode=mode,shape='usize result; &mut [u8;216] output; usize offset',local_records_only=True,not_native_credit=True),indent=1)+'\n')
