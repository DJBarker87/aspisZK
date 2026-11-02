from pathlib import Path
import sys,subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative';corrupt_reply=sys.argv[1]=='corrupt_reply'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('fn validate_common(');z=frozen.index('\n}',a)+2;old=frozen[a:z]
new=old.replace('fn validate_common(common: CommonPublicV1)', 'fn NEL_common_validator(common: CommonPublicV1, frame:&mut NEL_common_validator::Frame)').replace('digest_is_canonical(&common.anchor_root)','NEL_common_validator::canonical(&common.anchor_root,frame)').replace('digest_is_canonical(&common.nullifier)','NEL_common_validator::canonical(&common.nullifier,frame)')
project=new.replace('fn NEL_common_validator(common: CommonPublicV1, frame:&mut NEL_common_validator::Frame)','fn validate_common(common: CommonPublicV1)').replace('NEL_common_validator::canonical(&common.anchor_root,frame)','digest_is_canonical(&common.anchor_root)').replace('NEL_common_validator::canonical(&common.nullifier,frame)','digest_is_canonical(&common.nullifier)');assert project==old
ensures='*r==NEL_common_validator::reference(common,frame) && frame.log==NEL_common_validator::calls(common,frame)'
if negative:ensures='!('+ensures+')'
attrs='\n#[cfg(kani)]\n#[kani::requires(frame.log==0 && common==frame.expected)]\n#[kani::modifies(&mut frame.log)]\n#[kani::ensures(|r| '+ensures+')]\n'
# CommonPublicV1 lacks PartialEq? exact equality is expressed fieldwise below.
attrs=attrs.replace('common==frame.expected','common.pool==frame.expected.pool && common.deployment_domain==frame.expected.deployment_domain && common.anchor_sequence==frame.expected.anchor_sequence && common.anchor_root==frame.expected.anchor_root && common.nullifier==frame.expected.nullifier && common.asset_id==frame.expected.asset_id')
body='''use super::*;
pub(super) struct Frame{pub expected:CommonPublicV1,pub a:bool,pub b:bool,pub log:usize}
pub(super) fn canonical(d:&Digest,f:&mut Frame)->bool{assert!(f.log<2);let want=if f.log==0{&f.expected.anchor_root}else{&f.expected.nullifier};let k:usize=kani::any();kani::assume(k<8);assert!(d[k].0==want[k].0,"same common canonical argument and order");let r=if f.log==0{f.a}else{f.b};f.log+=1;r}
pub(super) fn reference(common:CommonPublicV1,f:&Frame)->Result<(),PoolV1PaymentStatementFormatError>{
 if common.pool==[0;32]||common.deployment_domain==[0;32]{Err(PoolV1PaymentStatementFormatError::ZeroRequiredBinding)}
 else if common.anchor_sequence>POOL_V1_LEAF_CAPACITY{Err(PoolV1PaymentStatementFormatError::InvalidAnchorSequence)}
 else if !f.a||!f.b{Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest)}
 else if common.asset_id.0>=P{Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId)}else{Ok(())}}
pub(super) fn calls(c:CommonPublicV1,f:&Frame)->usize{if c.pool==[0;32]||c.deployment_domain==[0;32]||c.anchor_sequence>POOL_V1_LEAF_CAPACITY{0}else if !f.a{1}else{2}}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof_for_contract(NEL_common_validator)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn common_validator(){let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any())};let mut f=Frame{expected:c,a:kani::any(),b:kani::any(),log:0};let _=NEL_common_validator(c,&mut f);}
'''
if corrupt_reply:
 assert body.count('f.log+=1;r}')==1
 body=body.replace('f.log+=1;r}','f.log+=1;!r}')
changed=frozen+attrs+new+'\n#[cfg(kani)]\n#[path="NEL_common_validator.rs"]\nmod NEL_common_validator;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_common_validator.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_COMMON_VALIDATOR_CURRENT.json').write_text(json.dumps(dict(negative=negative,corrupt_reply=corrupt_reply,source=path,frozen_body_sha256=hashlib.sha256(old.encode()).hexdigest(),exact_body_projection=project==old,all_typed_inputs=True,arbitrary_bool_children=True,full_result=True,ordered_effects=True,external_modifies=[],child_domain='every typed Digest; no canonicality assumption',trust_classification='P6/D188 option A reclassification'),indent=1)+'\n')
