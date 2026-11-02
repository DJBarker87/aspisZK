"""All-length scalar guard and exact validator call of the encoders."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','after'];subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile' if case=='live' else 'pair_terminal';p='crates/aspis-statement/src/pool_v1/'+file+'.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
Ty='PoolV1PairLiveSnapshotV1' if case=='live' else 'PoolV1PairVerifiedAfterstateV1';Err='PoolV1PairLiveSnapshotErrorV1' if case=='live' else 'PoolV1PairVerifierTransportErrorV1';fn='encode_pool_v1_pair_live_snapshot_v1' if case=='live' else 'encode_pool_v1_pair_verified_afterstate_v1';a=f.index('pub fn '+fn+'(');z=f.index('\n}',a)+2;original=f[a:z]
patch=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();error=next(l[1:] for l in patch.splitlines() if l.startswith('+fn NEE_any_'+Err+'(')).replace('NEE_any_'+Err,'any_error')
if case=='after':
 tree=next(l[1:] for l in patch.splitlines() if l.startswith('+fn NEE_any_PoolV1TreeError('));error=tree+'\n'+error
reply='if f.reply.is_ok(){Err(ERROR::'+('TreeFull' if case=='live' else 'InvalidAfterstateIndex')+')}else{Ok(())}' if negative else 'f.reply'
body='''use super::*;
use crate::pool_v1::*;
use aspis_core::field::M31;
use crate::Digest;
struct Frame<'a>{expected:&'a TYPE,reply:Result<(),ERROR>,called:bool,reached:bool}
fn child(s:&TYPE,f:&mut Frame)->Result<(),ERROR>{assert!(!f.called&&core::ptr::eq(s,f.expected),"same exact encoder validator input");f.called=true;REPLY}
fn prefix(s:&TYPE,length:usize,f:&mut Frame)->Result<(),ERROR>{GUARDchild(s,f)?;f.reached=true;Ok(())}
ERRORFN
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn encode_prefix(){let s=CONSTRUCT;let length:usize=kani::any();let mut f=Frame{expected:&s,reply:if kani::any(){Ok(())}else{Err(any_error())},called:false,reached:false};let actual=prefix(&s,length,&mut f);let expected=EXPECTED;assert!(actual==expected && f.called==CALLED && f.reached==actual.is_ok(),"exact encoder rejection prefix and untouched-output continuation");}
'''.replace('TYPE',Ty).replace('REPLY',reply).replace('ERRORFN',error).replace('ERROR',Err).replace('GUARD','if length!=800{return Err(PoolV1PairLiveSnapshotErrorV1::WrongLength);}' if case=='live' else '').replace('EXPECTED','if length!=800{Err(PoolV1PairLiveSnapshotErrorV1::WrongLength)}else{f.reply}' if case=='live' else 'f.reply').replace('CALLED','(length==800)' if case=='live' else 'true')
construct='PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:[NODES]}' if case=='live' else 'PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}'
body=body.replace('CONSTRUCT',construct.replace('NODES',','.join(['digest()']*20)))
changed=f+'\n#[cfg(kani)]\n#[path="NEM_encode_prefix.rs"]\nmod NEM_encode_prefix;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_encode_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_ENCODE_PREFIX_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),all_typed_inputs=True,all_usize_lengths=True,no_write_before_success=True,classification='length descriptor scalar guard and same actual validator borrow; successful byte suffix is separate'),indent=1)+'\n')
