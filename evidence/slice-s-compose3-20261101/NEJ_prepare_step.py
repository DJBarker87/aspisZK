"""Native one-iteration cut of the PINNED KMX copy, never a replacement stub."""
from pathlib import Path
import subprocess,difflib,json,hashlib,sys
E=Path(__file__).resolve().parent;slot=int(sys.argv[1]);negative=sys.argv[2]=='negative'
assert slot in [0,4,5,6,7,8,9]
subprocess.run([sys.executable,str(E/'NEJ_prepare_window.py'),str(slot),'positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
starts={0:0,4:8,5:40,6:72,7:80,8:112,9:144};sizes={0:4,4:32,5:32,6:8,7:32,8:32,9:4}
start=starts[slot];size=sizes[slot]
values={0:'magic',4:'common.pool',5:'common.deployment_domain',6:'common.anchor_sequence.to_le_bytes()',7:'reply0',8:'reply1',9:'common.asset_id.to_le_bytes()'}
expected=f'if j=={start}+offset{{({values[slot]})[offset]}}else{{old}}'
if negative:expected='('+expected+')^1'
module='''#![allow(non_snake_case,unused_variables)]
use super::*;
#[kani::requires(offset<SIZE && j<216 && old==output[j])]
#[kani::modifies(output)]
#[kani::ensures(|r| *r==offset+1 && output[j]==@EXPECTED@)]
fn step(output:&mut [u8;216],magic:[u8;4],common:CommonPublicV1,reply0:[u8;32],reply1:[u8;32],offset:usize,j:usize,old:u8)->usize{
 let dst=&mut output[START..END];let src=&(@VALUE@);let mut i=offset;
 dst[i]=src[i];i+=1;
 i
}
fn digest()->Digest {[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof_for_contract(step)]
fn common_window(){
 let mut output:[u8;216]=kani::any();let j:usize=kani::any();kani::assume(j<216);let old=output[j];
 let offset:usize=kani::any();kani::assume(offset<SIZE);
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any())};
 step(&mut output,kani::any(),c,kani::any(),kani::any(),offset,j,old);
}
'''.replace('SIZE',str(size)).replace('START',str(start)).replace('END',str(start+size)).replace('@VALUE@',values[slot]).replace('@EXPECTED@',expected)
# Assert this is exactly the selected KMX loop-body value operation, with a
# local offset on the exact frozen caller slice; it is never installed as stub.
kmx=subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'],text=True)
assert 'dst[i]=src[i];i+=1;' in kmx
assert '#[kani::stub' not in module and 'static ' not in module
changed=frozen+'\n#[cfg(kani)]\n#[path="NEJ_common_window.rs"]\nmod NEJ_common_window;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEJ_common_window.rs\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in module.splitlines())
(E/'NEJ_native_contracts.patch').write_text(patch)
p=json.loads((E/'NEJ_WINDOW_CURRENT.json').read_text());p.update(one_iteration=True,negative=negative,kmx_body='dst[i]=src[i];i+=1;',no_replacement_stub=True,loop_invariant='0 <= offset < width; arbitrary complete destination prestate and observation byte',step_modifies='output only',composition='NEJ_CommonFrame.run_spec and KMX_CopyMeaning.loop_spec; emitted setSlice frame in NEJ_ArrayFrame')
(E/'NEJ_WINDOW_CURRENT.json').write_text(json.dumps(p,indent=1)+'\n')
