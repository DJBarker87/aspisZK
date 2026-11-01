from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];assert case in ['snapshot','after'];negative=mode=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
P=E.parent/'slice-s-compose2-20261029';p=(P/'NEE_K052-NEE_oracle.patch').read_text();first=p.split('--- a/',1)[0];utilities='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n';utilities=utilities[:utilities.index('#[derive(Clone,Copy,Debug,PartialEq,Eq)]')].replace('NEE_','NEL_')
utilities=utilities.replace('use super::*;', 'use super::*;\nuse crate::pool_v1::*;\nuse crate::pool_v1::pair_forest_terminal::*;\nuse aspis_core::field::M31;\nuse crate::Digest;')
if case=='snapshot':
 needle='&mut output[32..32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]';assert needle in frozen
 body='''
struct Frame<'a>{expected:&'a PoolV1PairLiveSnapshotV1,window:*mut u8,index:usize,before:u8,write:u8,reply:Result<(),PoolV1PairLiveSnapshotErrorV1>,called:bool}
fn child(s:&PoolV1PairLiveSnapshotV1,out:&mut[u8],f:&mut Frame)->Result<(),PoolV1PairLiveSnapshotErrorV1>{assert!(!f.called&&core::ptr::eq(s,f.expected),"same live snapshot receiver");assert!(out.len()==800 && out.as_mut_ptr()==f.window,"same child physical window");assert!(out[f.index]==f.before,"same child prestate cell");out[f.index]=f.write;f.called=true;f.reply}
#[kani::proof]
fn binding(){let s=NEL_common().lane_transition;let mut output:[u8;1520]=kani::any();let index:usize=kani::any();kani::assume(index<800);let old=output[32+index];let change:u8=kani::any();let mut f=Frame{expected:&s.live_snapshot,window:output.as_mut_ptr().wrapping_add(32),index,before:old,write:change,reply:if kani::any(){Ok(())}else{Err(NEL_any_PoolV1PairLiveSnapshotErrorV1())},called:false};let r=child(&s.live_snapshot,&mut output[START..START+800],&mut f);assert!(r==f.reply && f.called && output[32+index]==change,"same Result and indexed mutation");}
'''.replace('START','33' if negative else '32')
else:
 needle='encode_pool_v1_pair_verified_afterstate_v1(&statement.candidate_afterstate)';assert needle in frozen
 body='''
struct Frame<'a>{expected:&'a PoolV1PairVerifiedAfterstateV1,reply:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>,called:bool}
fn child(s:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(!f.called&&core::ptr::eq(s,f.expected),"same afterstate receiver");f.called=true;f.reply}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn binding(){let s=NEL_common().lane_transition;let other=NEL_common().lane_transition.candidate_afterstate;let reply:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>=if kani::any(){Ok(kani::any())}else{Err(NEL_any_PoolV1PairVerifierTransportErrorV1())};let mut f=Frame{expected:&s.candidate_afterstate,reply,called:false};let r=child(ARG,&mut f);assert!(f.called);match (r,reply){(Ok(actual),Ok(want))=>{let j:usize=kani::any();kani::assume(j<688);assert!(actual[j]==want[j]);},(Err(a),Err(b))=>assert!(a==b),_=>assert!(false)}}
'''.replace('ARG','&other' if negative else '&s.candidate_afterstate')
body=utilities+body
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_late_binding.rs"]\nmod NEL_late_binding;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_late_binding.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_LATE_BINDING_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=path,source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),frozen_call=needle,whole_return_or_indexed_mutation=True,arbitrary_full_Result=True,no_stub_verified=True,classification='actual typed call-place/window association; snapshot mutation is ONE arbitrary indexed cell and needs universal frame/induction, not an arbitrary full-mutation caller certificate by itself'),indent=1)+'\n')
