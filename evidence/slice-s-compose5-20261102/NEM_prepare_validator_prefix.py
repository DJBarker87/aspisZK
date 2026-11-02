"""Exact scalar/rejection prefix before the frontier loop, arbitrary root reply."""
from pathlib import Path
import sys,subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','after']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile' if case=='live' else 'pair_terminal';p='crates/aspis-statement/src/pool_v1/'+file+'.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
Ty='PoolV1PairLiveSnapshotV1' if case=='live' else 'PoolV1PairVerifiedAfterstateV1';Err='PoolV1PairLiveSnapshotErrorV1' if case=='live' else 'PoolV1PairVerifierTransportErrorV1';root='current_root' if case=='live' else 'next_root';fn='validate_pool_v1_pair_live_snapshot_v1' if case=='live' else 'validate_verified_afterstate';a=f.index('fn '+fn+'(');z=f.index('\n}',a)+2;original=f[a:z]
prefix=original[:original.index('    let mut level = 0;')];name='snapshot' if case=='live' else 'afterstate';child=('' if case=='live' else 'super::pair_tree_profile::')+'digest_is_canonical(&'+name+'.'+root+')'
new=prefix.replace('fn '+fn+'(','fn prefix(').replace(name+': &'+Ty+',',name+': &'+Ty+',\n    frame:&mut Frame,').replace(child,'child(&'+name+'.'+root+',frame)')+'    frame.reached=true;\n    Ok(())\n}'
ref=prefix.replace('fn '+fn+'(','fn reference(').replace(name+': &'+Ty+',',name+': &'+Ty+',\n    reply:bool,').replace(child,'reply')+'    Ok(())\n}'
# The native actual root borrow is checked at the child; local reply is arbitrary.
body='''use super::*;
use aspis_core::field::M31;
use crate::Digest;
struct Frame<'a>{expected:&'a Digest,reply:bool,called:bool,reached:bool}
fn child(d:&Digest,f:&mut Frame)->bool{assert!(!f.called&&core::ptr::eq(d,f.expected),"same exact validator root digest");f.called=true;REPLY}
NATIVE
REFERENCE
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn validator_prefix(){let s=CONSTRUCT;let mut f=Frame{expected:&s.ROOT,reply:kani::any(),called:false,reached:false};let actual=prefix(&s,&mut f);let expected=reference(&s,f.reply);assert!(actual==expected && f.reached==actual.is_ok(),"exact validator prefix Result and continuation");}
'''.replace('REPLY','!f.reply' if negative else 'f.reply').replace('NATIVE',new).replace('REFERENCE',ref).replace('ROOT',root)
construct='PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:[NODES]}' if case=='live' else 'PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}'
body=body.replace('CONSTRUCT',construct.replace('NODES',','.join(['digest()']*20)))
if case=='after':body=body.replace('super::POOL_V1_PAIR_CAPACITY','super::super::POOL_V1_PAIR_CAPACITY')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_validator_prefix.rs"]\nmod NEM_validator_prefix;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_validator_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_VALIDATOR_PREFIX_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=p,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),prefix_source=prefix,exact_projection=True,arbitrary_root_reply=True,all_typed_inputs=True,empty_external_modifies=True,classification='scalar rejection prefix ending at explicit frontier-loop continuation, not a whole-buffer run'),indent=1)+'\n')
