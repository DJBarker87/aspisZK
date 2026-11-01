from pathlib import Path
import sys,subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:3];control_only=len(sys.argv)>3 and sys.argv[3]=='control';negative=mode=='negative';assert case in ['transfer','withdrawal']
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
fn='validate_pool_v1_'+('private_transfer' if case=='transfer' else 'withdrawal')+'_public_v1'
a=frozen.index('pub fn '+fn+'(');z=frozen.index('\n}',a)+2;old=frozen[a:z]
Ty='PoolV1'+('PrivateTransfer' if case=='transfer' else 'Withdrawal')+'PublicV1'
new=old.replace('pub fn '+fn+'(','fn NEL_payment_validator(').replace('public: &'+Ty+',','public: &'+Ty+',\n    frame:&mut NEL_payment_validator::Frame,')
new=new.replace('validate_common('+case+'_common(public))','NEL_payment_validator::common('+case+'_common(public),frame)')
for field in ['recipient_commitment','change_commitment']:new=new.replace('digest_is_canonical(&public.'+field+')','NEL_payment_validator::canonical(&public.'+field+',frame)')
# Reference preserves all primitive branch order, replacing only closed children.
ref=old.replace('pub fn '+fn+'(','pub(super) fn reference(').replace('public: &'+Ty+',','public: &'+Ty+',\n    frame:&Frame,')
ref=ref.replace('validate_common('+case+'_common(public))','frame.reply')
ref=ref.replace('digest_is_canonical(&public.recipient_commitment)','frame.a').replace('digest_is_canonical(&public.change_commitment)','frame.b' if case=='transfer' else 'frame.a')
added=[]
for line in ref.splitlines():
 if line.startswith('pub(super) fn reference'):added.append(line)
 else:added.append(line)
ref='\n'.join(added)
project=new.replace('fn NEL_payment_validator(','pub fn '+fn+'(').replace('    frame:&mut NEL_payment_validator::Frame,\n','').replace('NEL_payment_validator::common('+case+'_common(public),frame)','validate_common('+case+'_common(public))')
for field in ['recipient_commitment','change_commitment']:project=project.replace('NEL_payment_validator::canonical(&public.'+field+',frame)','digest_is_canonical(&public.'+field+')')
assert project==old
ensures='*r==NEL_payment_validator::reference(public,frame) && frame.log==NEL_payment_validator::calls(public,frame)'
if negative:ensures='!('+ensures+')'
attrs='\n#[cfg(kani)]\n#[kani::requires(frame.log==0)]\n#[kani::modifies(&mut frame.log)]\n#[kani::ensures(|r| '+ensures+')]\n'
condition='frame.log==0 && frame.expected.pool==public.pool && frame.expected.deployment_domain==public.deployment_domain && frame.expected.anchor_sequence==public.anchor_sequence && frame.expected.anchor_root==public.anchor_root && frame.expected.nullifier==public.nullifier && frame.expected.asset_id==public.asset_id && frame.x==public.'+('recipient_commitment' if case=='transfer' else 'change_commitment')+' && frame.y==public.change_commitment'
attrs=attrs.replace('frame.log==0',condition)
# Keep arbitrary callees and the exact actual selected arguments in local frame.
P=E.parent/'slice-s-compose2-20261029';patch0=(P/'NEE_K052-NEE_oracle.patch').read_text();first=patch0.split('--- a/',1)[0]
utilities='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
error=next(l for l in utilities.splitlines() if l.startswith('fn NEE_any_PoolV1PaymentStatementFormatError'))
error=error.replace('NEE_any_PoolV1PaymentStatementFormatError','any_error')
checks='c.pool==f.expected.pool && c.deployment_domain==f.expected.deployment_domain && c.anchor_sequence==f.expected.anchor_sequence && c.anchor_root==f.expected.anchor_root && c.nullifier==f.expected.nullifier && c.asset_id==f.expected.asset_id'
canon='p.recipient_commitment' if case=='transfer' else 'p.change_commitment'
construct='recipient_commitment:digest(),change_commitment:digest()' if case=='transfer' else 'amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()'
calls='if f.reply.is_err(){1}else if !f.a{2}else{3}' if case=='transfer' else 'if f.reply.is_err()||p.amount==0||p.amount>=VALUE_LIMIT||p.destination_token_account==[0;32]{1}else{2}'
body='''use super::*;
pub(super) struct Frame{pub expected:CommonPublicV1,pub x:Digest,pub y:Digest,pub reply:Result<(),PoolV1PaymentStatementFormatError>,pub a:bool,pub b:bool,pub log:usize}
pub(super) fn common(c:CommonPublicV1,f:&mut Frame)->Result<(),PoolV1PaymentStatementFormatError>{assert!(f.log==0 && CHECKS,"same complete payment common argument");f.log=1;f.reply}
pub(super) fn canonical(d:&Digest,f:&mut Frame)->bool{assert!(f.log>=1&&f.log<3);let want=if f.log==1{&f.x}else{&f.y};let k:usize=kani::any();kani::assume(k<8);assert!(d[k].0==want[k].0,"same payment digest and call order");let r=if f.log==1{f.a}else{f.b};f.log+=1;r}
REF
pub(super) fn calls(p:&TYPE,f:&Frame)->usize{CALLS}
ERROR
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof_for_contract(NEL_payment_validator)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn payment_validator(){let p=TYPE{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),CONSTRUCT};let mut f=Frame{expected:COMMON(&p),x:CANON,y:p.change_commitment,reply:if kani::any(){Ok(())}else{Err(any_error())},a:kani::any(),b:kani::any(),log:0};let _=NEL_payment_validator(&p,&mut f);}
'''.replace('CHECKS',checks).replace('REF',ref).replace('TYPE',Ty).replace('CALLS',calls).replace('ERROR',error).replace('CONSTRUCT',construct).replace('COMMON',case+'_common').replace('CANON',canon)
if control_only:
 attrs=attrs.replace(condition,'frame.log==0')
 body=body.replace('pub expected:CommonPublicV1,pub x:Digest,pub y:Digest,','')
 common_start=body.index('pub(super) fn common(');common_end=body.index('\n',common_start)
 body=body[:common_start]+'pub(super) fn common(_c:CommonPublicV1,f:&mut Frame)->Result<(),PoolV1PaymentStatementFormatError>{assert!(f.log==0);f.log=1;f.reply}'+body[common_end:]
 canon_start=body.index('pub(super) fn canonical(');canon_end=body.index('\n',canon_start)
 body=body[:canon_start]+'pub(super) fn canonical(_d:&Digest,f:&mut Frame)->bool{assert!(f.log>=1&&f.log<3);let r=if f.log==1{f.a}else{f.b};f.log+=1;r}'+body[canon_end:]
 body=body.replace('expected:'+case+'_common(&p),x:'+canon+',y:p.change_commitment,','')
changed=frozen+attrs+new+'\n#[cfg(kani)]\n#[path="NEL_payment_validator.rs"]\nmod NEL_payment_validator;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_payment_validator.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_PAYMENT_VALIDATOR_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,control_only=control_only,argument_binding='separate obligation' if control_only else 'checked by local exact-argument frame',source=path,frozen_body_sha256=hashlib.sha256(old.encode()).hexdigest(),exact_body_projection=True,caller_frame_domain='selected actual child arguments; currently constructed from same caller, proof_for_contract requires these input relationships explicitly if used as a contract',all_child_Results=True,local_logs=True,empty_external_modifies=True),indent=1)+'\n')
