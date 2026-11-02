"""One real live/after encoder field, arbitrary prestate, KMX indexed step."""
from pathlib import Path
import sys,subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,slot,mode=sys.argv[1:];slot=int(slot);negative=mode=='negative';wrong=mode=='wrong_place';assert case in ['live','after']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile' if case=='live' else 'pair_terminal';p='crates/aspis-statement/src/pool_v1/'+file+'.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
Ty='PoolV1PairLiveSnapshotV1' if case=='live' else 'PoolV1PairVerifiedAfterstateV1';N=800 if case=='live' else 688
# start, width, exact field/scalar expression; child digest reply only in last slot.
windows=([(0,8,'POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC'),(8,1,'POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION'),(16,32,'POOL_V1_PAIR_TREE_FORMAT_BINDING'),(48,32,'s.pool'),(80,32,'s.deployment_domain'),(112,8,'s.sequence.to_le_bytes()'),(120,8,'s.next_pair_index.to_le_bytes()'),(128,32,'CHILD')] if case=='live' else [(0,4,'POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC'),(4,1,'POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION'),(5,1,'crate::pool_v1::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION'),(6,1,'POOL_V1_DIGEST_ENCODING_VERSION'),(7,1,'1u8'),(8,8,'s.next_pair_index.to_le_bytes()'),(16,32,'CHILD')])
start,width,expr=windows[slot];root='current_root' if case=='live' else 'next_root';frontier='frontier' if case=='live' else 'next_frontier'
fn='encode_pool_v1_pair_live_snapshot_v1' if case=='live' else 'encode_pool_v1_pair_verified_afterstate_v1';a=f.index('pub fn '+fn+'(');z=f.index('\n}',a)+2;original=f[a:z]
assert ('output['+str(start)) in original or start==0
# Child receives the actual root, and the arbitrary reply feeds this window.
setup='';src_expr=expr
if expr=='CHILD':setup='let reply=child(&s.'+root+',&s.'+frontier+'[0]' if wrong else 'let reply=child(&s.'+root+',&s.'+root
if expr=='CHILD':setup+=',&mut called,reply);';src_expr='reply'
if width==1:
 operation=f'output[{start}]=({expr})'+('^1' if negative else '')+';'
 expected=f'if j=={start}{{{expr}}}else{{old}}';offset='';stepcheck=''
else:
 operation=f'let src=&({src_expr});let dst=&mut output[{start}..{start+width}];let mut i=offset;dst[i]=src[i]'+('^1' if negative else '')+';i+=1;'
 expected=f'if j=={start}+offset{{({src_expr})[offset]}}else{{old}}';offset=f'let offset:usize=kani::any();kani::assume(offset<{width});';stepcheck='assert!(i==offset+1);'
body='''use super::*;
use aspis_core::field::M31;
use crate::Digest;
fn child(d:&Digest,want:&Digest,called:&mut bool,reply:[u8;32])->[u8;32]{assert!(!*called&&core::ptr::eq(d,want),"same actual root at encoder child call");*called=true;reply}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn encoder_window(){let s=CONSTRUCT;let mut output:[u8;SIZE]=kani::any();let j:usize=kani::any();kani::assume(j<SIZE);let old=output[j];OFFSETlet mut called=false;let reply:[u8;32]=kani::any();
 SETUP
 OPERATION
 STEPCHECK
 assert!(output[j]==EXPECTED,"same caller field byte and full prestate frame");
 CALLCHECK
}
'''.replace('SIZE',str(N)).replace('OFFSET',offset).replace('SETUP',setup).replace('OPERATION',operation).replace('STEPCHECK',stepcheck).replace('EXPECTED',expected).replace('CALLCHECK','assert!(called);' if expr=='CHILD' else '')
construct='PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:[NODES]}' if case=='live' else 'PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}'
body=body.replace('CONSTRUCT',construct.replace('NODES',','.join(['digest()']*20)))
changed=f+'\n#[cfg(kani)]\n#[path="NEM_encoder_window.rs"]\nmod NEM_encoder_window;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_encoder_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_ENCODER_WINDOW_CURRENT.json').write_text(json.dumps(dict(case=case,slot=slot,mode=mode,start=start,width=width,expression=expr,destination_width=N,source=p,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),all_typed_inputs=True,arbitrary_prestate=True,full_frame=True,one_KMX_iteration=width!=1,classification='source field/scalar window; exact native child argument and arbitrary full digest reply for root; no whole-buffer loop'),indent=1)+'\n')
