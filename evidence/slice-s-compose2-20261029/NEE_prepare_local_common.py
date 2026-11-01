"""Re-establish the indexed common encoder frame using a local record."""
from pathlib import Path
import difflib,json,hashlib,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
negative=sys.argv[1]=='negative'
prefix=sys.argv[1]=='prefix'
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('fn encode_common(');z=frozen.index('\n}\n',a)+3;body=frozen[a:z]
threaded=body.replace('    common: CommonPublicV1,','    common: CommonPublicV1,\n    frame: &mut NEE_common_oracle::Frame,')
changes={f'encode_digest_canonical(&common.{n})':f'NEE_common_oracle::digest_reply(&common.{n},frame)' for n in ['anchor_root','nullifier']}
for before,after in changes.items():assert threaded.count(before)==1;threaded=threaded.replace(before,after)
project=threaded.replace('    frame: &mut NEE_common_oracle::Frame,\n','')
for before,after in changes.items():project=project.replace(after,before)
assert project==body
if prefix:
 end=threaded.index('    output[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]')
 threaded=threaded[:end]+'}\n'
expr='frame.log==2 && output[frame.j]==NEE_common_oracle::byte(magic,kind,common,frame)'
if prefix:expr='frame.log==0 && output[frame.j]==if frame.j<40 {NEE_common_oracle::byte(magic,kind,common,frame)}else{frame.old}'
if negative:expr='!('+expr+')'
attrs='''#[cfg(kani)]
#[kani::requires(frame.j<216 && frame.log==0 && frame.old==output[frame.j] && frame.e0==common.anchor_root && frame.e1==common.nullifier)]
#[kani::modifies(output, &mut frame.log)]
#[kani::ensures(|_| '''+expr+''')]
'''
changed=frozen[:a]+'#[cfg(not(kani))]\n'+body+attrs+threaded+frozen[z:]
for projector in ['transfer_common(public)','withdrawal_common(public)']:
 start=changed.index('    encode_common(\n',changed.index('pub fn encode_pool_v1_'+('private_transfer' if projector.startswith('transfer') else 'withdrawal')))
 end=changed.index('    );',start)+7
 call=changed[start:end]
 new=call.replace('        '+projector+',','        '+projector+',\n        &mut NEE_common_oracle::Frame::new('+projector+',0,0),')
 changed=changed[:start]+'    #[cfg(not(kani))]\n'+call+'\n    #[cfg(kani)]\n'+new+changed[end:]
changed+='\n#[cfg(kani)]\n#[path="NEE_common_oracle.rs"]\nmod NEE_common_oracle;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
base,hook=oracle_parts();utility=base[base.index('fn NEE_digest()'):base.index('fn NEE_common()')]
module='''#![allow(non_snake_case)]
use super::*;
'''+utility+'''
pub(super) struct Frame {pub j:usize,pub old:u8,pub log:usize,pub e0:Digest,pub e1:Digest,d0:[u8;32],d1:[u8;32]}
impl Frame{pub(super) fn new(c:CommonPublicV1,j:usize,old:u8)->Self {Self{j,old,log:0,e0:c.anchor_root,e1:c.nullifier,d0:kani::any(),d1:kani::any()}}}
pub(super) fn digest_reply(d:&Digest,f:&mut Frame)->[u8;32]{
 let k:usize=kani::any();kani::assume(k<8);assert!(f.log<2);
 assert!(d[k].0==if f.log==0{f.e0[k].0}else{f.e1[k].0},"NEE same digest call argument");
 let r=if f.log==0{f.d0}else{f.d1};f.log+=1;r
}
pub(super) fn byte(magic:[u8;4],kind:PoolV1TransitionKind,c:CommonPublicV1,f:&Frame)->u8{
 match f.j {0..=3=>magic[f.j],4=>1,5=>kind as u8,6=>1,7=>f.old,
 8..=39=>c.pool[f.j-8],40..=71=>c.deployment_domain[f.j-40],72..=79=>c.anchor_sequence.to_le_bytes()[f.j-72],
 80..=111=>f.d0[f.j-80],112..=143=>f.d1[f.j-112],144..=147=>c.asset_id.0.to_le_bytes()[f.j-144],_=>f.old}
}
#[kani::proof_for_contract(encode_common)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn common_oracle(){
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NEE_digest(),nullifier:NEE_digest(),asset_id:M31(kani::any())};
 let mut output:[u8;216]=kani::any();let magic:[u8;4]=kani::any();
 let kind=if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};
 let j:usize=kani::any();kani::assume(j<216);let mut frame=Frame::new(c,j,output[j]);
 encode_common(&mut output,magic,kind,c,&mut frame);
}
'''
name='crates/aspis-statement/src/pool_v1/NEE_common_oracle.rs'
patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(base.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in base.splitlines())+hook)
(E/'NEE_LOCAL_COMMON_PROJECTION.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source=path,body_sha256=hashlib.sha256(body.encode()).hexdigest(),exact_body_projection=project==body,threaded_calls=changes,original_harness_name='common_oracle',domain='all typed CommonPublicV1, both kinds, arbitrary output prestate and j<216; two full arbitrary digest replies',local_records_only=True,negative=negative,prefix_only=prefix,full_body_projection_before_split=project==body,matched_control_available=not prefix),indent=1)+'\n')
