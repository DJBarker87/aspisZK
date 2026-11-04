"""Isolate one frozen common-encoder statement; no whole-buffer solver join."""
from pathlib import Path
import subprocess,difflib,json,hashlib,sys
E=Path(__file__).resolve().parent
slot=int(sys.argv[1]);negative=sys.argv[2]=='negative'
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('fn encode_common(');z=frozen.index('\n}\n',a)+3;body=frozen[a:z]
statements=body[body.index('    output[..4]'):body.rindex('}')].split(';')
statements=[s.strip()+';' for s in statements if s.strip()]
assert len(statements)==10
stmt=statements[slot]
# Child evaluations are outside this window: full arbitrary fixed-array replies.
stmt=stmt.replace('encode_digest_canonical(&common.anchor_root)','reply0').replace('encode_digest_canonical(&common.nullifier)','reply1')
starts=[0,4,5,6,8,40,72,80,112,144];sizes=[4,1,1,1,32,32,8,32,32,4]
start=starts[slot];size=sizes[slot]
values=['magic[j]','POOL_V1_PAYMENT_STATEMENT_VERSION','kind as u8','POOL_V1_DIGEST_ENCODING_VERSION','common.pool[j-8]','common.deployment_domain[j-40]','common.anchor_sequence.to_le_bytes()[j-72]','reply0[j-80]','reply1[j-112]','common.asset_id.to_le_bytes()[j-144]']
expected=f'if {start}<=j && j<{start+size} {{{values[slot]}}}else{{old}}'
if negative:expected='('+expected+')^1'
module='''#![allow(non_snake_case,unused_variables)]
use super::*;
#[kani::requires(j<216 && old==output[j])]
#[kani::modifies(output)]
#[kani::ensures(|_| output[j]==EXPECTED)]
fn window(output:&mut [u8;216],magic:[u8;4],kind:PoolV1TransitionKind,common:CommonPublicV1,reply0:[u8;32],reply1:[u8;32],j:usize,old:u8){
 @BODY@
}
fn digest()->Digest {[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof_for_contract(window)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn common_window(){
 let mut output:[u8;216]=kani::any();let j:usize=kani::any();kani::assume(j<216);let old=output[j];
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any())};
 let kind=if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};
 window(&mut output,kani::any(),kind,c,kani::any(),kani::any(),j,old);
}
'''.replace('EXPECTED',expected).replace('@BODY@',stmt)
changed=frozen+'\n#[cfg(kani)]\n#[path="NEY_common_window.rs"]\nmod NEY_common_window;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_common_window.rs\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in module.splitlines())
(E/'NEY_native_contracts.patch').write_text(patch)
# The runner retains a pure constructor module hook, without historical logs.
base='#![allow(dead_code)]\n'
mp='crates/aspis-statement/src/pool_v1/mod.rs'
mf=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+mp],text=True)
hook=''.join(difflib.unified_diff(mf.splitlines(True),(mf+'\n#[cfg(kani)]\nmod NEY_oracle;\n').splitlines(True),fromfile='a/'+mp,tofile='b/'+mp))
(E/'NEY_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_oracle.rs\n@@ -0,0 +1,1 @@\n+'+base+hook)
(E/'NEY_WINDOW_CURRENT.json').write_text(json.dumps(dict(slot=slot,start=start,size=size,negative=negative,statement=statements[slot],window_statement=stmt,source=path,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),child_evaluations='two arbitrary replies; child evaluation correspondence separate',classification='sequential native statement window, indexed prestate frame; not a whole native root',exact_statement_projection=stmt==statements[slot] if slot not in (7,8) else True),indent=1)+'\n')
