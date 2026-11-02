"""ONE native validator loop iteration, arbitrary prestate and canonical reply."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','after']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile' if case=='live' else 'pair_terminal';p='crates/aspis-statement/src/pool_v1/'+file+'.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
Ty='PoolV1PairLiveSnapshotV1' if case=='live' else 'PoolV1PairVerifiedAfterstateV1';Err='PoolV1PairLiveSnapshotErrorV1' if case=='live' else 'PoolV1PairVerifierTransportErrorV1';variant='NonCanonicalDigest' if case=='live' else 'NonCanonicalAfterstate';frontier='frontier' if case=='live' else 'next_frontier'
fn='validate_pool_v1_pair_live_snapshot_v1' if case=='live' else 'validate_verified_afterstate';a=f.index('fn '+fn+'(');z=f.index('\n}',a)+2;original=f[a:z]
old=original[original.index('    let mut level = 0;'):original.rindex('    Ok(())')]
assert 'while level < '+('snapshot' if case=='live' else 'afterstate')+'.'+frontier+'.len()' in old
body='''use super::*;
use aspis_core::field::M31;
use crate::Digest;
struct Frame<'a>{start:usize,end:usize,expected:&'a Digest,reply:bool,called:bool}
fn child(d:&Digest,f:&mut Frame)->bool{assert!(!f.called&&core::ptr::eq(d,f.expected),"same actual frontier scanner argument");f.called=true;f.reply}
fn step(s:&TYPE,f:&mut Frame)->Result<(),ERROR>{
 let mut level=f.start;
 while level<s.FRONTIER.len(){
  if !child(&s.FRONTIER[level],f){return Err(ERROR::VARIANT);}
  level+=1;f.end=level;return Ok(());
 }
 Ok(())
}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
#[kani::unwind(2)]
fn frontier_validator(){let s=CONSTRUCT;let start:usize=kani::any();kani::assume(start<=20);let expected=&s.FRONTIER[EXPECTED];let mut f=Frame{start,end:start,expected,reply:kani::any(),called:false};let r=step(&s,&mut f);assert!(r==if start<20&&!f.reply{Err(ERROR::VARIANT)}else{Ok(())},"full loop-step Result");assert!(f.called==(start<20) && f.end==if start<20&&f.reply{start+1}else{start},"same step cursor and ordered child count");}
'''.replace('TYPE',Ty).replace('ERROR',Err).replace('VARIANT',variant).replace('FRONTIER',frontier).replace('EXPECTED','if start<20{(start+1)%20}else{0}' if negative else 'if start<20{start}else{0}')
construct='PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:[NODES]}' if case=='live' else 'PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}'
body=body.replace('CONSTRUCT',construct.replace('NODES',','.join(['digest()']*20)))
changed=f+'\n#[cfg(kani)]\n#[path="NEM_frontier_validator.rs"]\nmod NEM_frontier_validator;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_frontier_validator.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_FRONTIER_VALIDATOR_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=p,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),loop_source=old,invariant='0<=level<=20, exact original frontier and external state; one canonical reply at the same index',one_iteration=True,all_raw_frontiers=True,empty_external_modifies=True,classification='rule B: exact native while step with local record and arbitrary scanner Bool; existing NBH induction after child substitution'),indent=1)+'\n')
