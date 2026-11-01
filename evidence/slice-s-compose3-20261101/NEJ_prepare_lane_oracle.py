"""Exact frozen output-lane caller, scalar oracles with local ordered logs."""
from pathlib import Path
import subprocess,difflib,json
E=Path(__file__).resolve().parent
subprocess.run(['python3',str(E/'NEJ_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('pub fn pool_v1_pair_forest_output_lane_v1(');z=frozen.index('\n}\n',a)+3;old=frozen[a:z]
new=old.replace('    nullifier: &Digest,','    nullifier: &Digest,\n    frame: &mut NEJ_lane_oracle::Frame,').replace('digest_is_canonical(nullifier)','NEJ_lane_oracle::canonical(nullifier,frame)').replace('first_canonical_byte(nullifier)','NEJ_lane_oracle::first(nullifier,frame)')
project=new.replace('    frame: &mut NEJ_lane_oracle::Frame,\n','').replace('NEJ_lane_oracle::canonical(nullifier,frame)','digest_is_canonical(nullifier)').replace('NEJ_lane_oracle::first(nullifier,frame)','first_canonical_byte(nullifier)');assert project==old
# Keep the ordinary public signature for every unrelated frozen caller. The
# cfg-only threaded copy is the exact source cut under examination.
new=new.replace('pub fn pool_v1_pair_forest_output_lane_v1(','fn NEJ_threaded_lane(')
attrs='''#[cfg(kani)]
#[kani::requires(frame.log==0 && *nullifier==frame.expected)]
#[kani::modifies(&mut frame.log)]
#[kani::ensures(|r| *r==if frame.canon {Ok(frame.byte&7)}else{Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)} && frame.log==if frame.canon{2}else{1})]
'''
changed=frozen+'\n'+attrs+new+'\n#[cfg(kani)]\n#[path="NEJ_lane_oracle.rs"]\nmod NEJ_lane_oracle;\n'
body='''#![allow(non_snake_case)]
use super::*;
use aspis_core::field::M31;
pub(super) struct Frame{pub expected:Digest,pub canon:bool,pub byte:u8,pub log:usize}
pub(super) fn canonical(d:&Digest,f:&mut Frame)->bool{let k:usize=kani::any();kani::assume(k<8);assert!(f.log==0 && d[k].0==f.expected[k].0);f.log=1;f.canon}
pub(super) fn first(d:&Digest,f:&mut Frame)->u8{let k:usize=kani::any();kani::assume(k<8);assert!(f.log==1 && f.canon && d[k].0==f.expected[k].0);f.log=2;f.byte}
#[kani::proof_for_contract(NEJ_threaded_lane)]
fn lane_oracle(){let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut f=Frame{expected:d,canon:kani::any(),byte:kani::any(),log:0};let _=NEJ_threaded_lane(&d,&mut f);}
'''
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEJ_lane_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEJ_native_contracts.patch').write_text(patch)
(E/'NEJ_LANE_PROJECTION.json').write_text(json.dumps(dict(source=path,exact_body_projection=project==old,full_result=True,arbitrary_scalar_replies=True,local_logs=True,ordered_effects=True,frame='only local log; empty native output mutation',matched_control='OPEN; no credit without matching failing control',child_domains='OPEN: arbitrary digest must be instantiated in selected child domain'),indent=1)+'\n')
