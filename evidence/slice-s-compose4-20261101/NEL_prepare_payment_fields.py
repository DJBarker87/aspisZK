from pathlib import Path
import sys,json,subprocess,difflib,hashlib
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
for phrase in ['digest_is_canonical(&public.recipient_commitment)','digest_is_canonical(&public.change_commitment)','validate_common(transfer_common(public))','validate_common(withdrawal_common(public))']:assert phrase in frozen
body='''use super::*;
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
fn recipient(p:&PoolV1PrivateTransferPublicV1)->&Digest{&p.FIELD}
fn transfer_change(p:&PoolV1PrivateTransferPublicV1)->&Digest{&p.FIELD_CHANGE_T}
fn withdrawal_change(p:&PoolV1WithdrawalPublicV1)->&Digest{&p.FIELD_CHANGE_W}
#[kani::proof]
fn field_binding(){let mode:u8=kani::any();kani::assume(mode<4);match mode{
0=>assert!(super::super::pair_forest_accounts::NEL_lane_relation()),
1=>assert!(super::super::pair_forest_accounts::NEL_first_relation()),
2=>{ let t=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 let field:u8=kani::any();kani::assume(field<3);match field{
 0=>assert!(core::ptr::eq(recipient(&t),&t.recipient_commitment),"actual transfer recipient place"),
 1=>assert!(core::ptr::eq(transfer_change(&t),&t.change_commitment),"actual transfer change place"),
 _=>assert!(core::ptr::eq(withdrawal_change(&w),&w.change_commitment),"actual withdrawal change place")}},
_=>{let mut out:[u8;32]=kani::any();let start:usize=kani::any();let width:usize=kani::any();kani::assume(start<=32&&width<=32-start&&width>0);let offset:usize=kani::any();kani::assume(offset<width);let j:usize=kani::any();kani::assume(j<32);let old=out[j];let value:u8=kani::any();let dst=&mut out[start..start+width];let src=&[value];let mut i=offset;dst[i]=src[0]CELL_CORRUPTION;i+=1;assert!(i==offset+1);assert!(out[j]==if j==start+offset{value}else{old});}
}}

'''.replace('FIELD_CHANGE_T','recipient_commitment' if negative else 'change_commitment').replace('FIELD_CHANGE_W','nullifier' if negative else 'change_commitment').replace('FIELD','change_commitment' if negative else 'recipient_commitment').replace('CELL_CORRUPTION','^1' if negative else '')
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_payment_fields.rs"]\nmod NEL_payment_fields;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_payment_fields.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
# Strengthen the output-lane caller control in the same serial scope. The
# actual original target names/body are retained; only the oracle reply flips.
forest='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'
ff=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+forest],text=True)
oldpatch=(E/'NEL_K002-NEL_native_contracts.patch').read_text()
first,rest=oldpatch.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_lane_oracle.rs\n',1)
append=''.join(l[1:]+'\n' for l in first.splitlines() if l.startswith('+') and not l.startswith('+++'))
fb=''.join(l[1:]+'\n' for l in rest.splitlines() if l.startswith('+'))
if negative:
 assert fb.count('f.log=2;f.byte}')==1
 fb=fb.replace('f.log=2;f.byte}','f.log=2;f.byte^1}')
helper='\n#[cfg(kani)]\npub(super) fn NEL_lane_relation()->bool {let d=['+','.join(['aspis_core::field::M31(kani::any())']*8)+'];let mut f=NEL_lane_oracle::Frame{expected:d,canon:kani::any(),byte:kani::any(),log:0};let r=NEL_threaded_lane(&d,&mut f);(r==(if f.canon{Ok(f.byte&7)}else{Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)})) && f.log==(if f.canon{2}else{1})}\n'
firstpatch=(E/'NEL_K030-NEL_native_contracts.patch').read_text()
fhead,frest=firstpatch.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_first.rs\n',1)
fappend=''.join(l[1:]+'\n' for l in fhead.splitlines() if l.startswith('+') and not l.startswith('+++'))
# K030 appended only a hook, because its threaded caller is inside NEL_first.
fbody=''.join(l[1:]+'\n' for l in frest.splitlines() if l.startswith('+'))
fbody=fbody.replace('struct Frame{','pub(super) struct Frame{').replace('expected:Digest,reply:[u8;32],called:bool','pub expected:Digest,pub reply:[u8;32],pub called:bool')
fbody=fbody.replace('fn threaded_first(','pub(super) fn threaded_first(')
if negative:
 assert fbody.count('f.called=true;f.reply}')==1
 fbody=fbody.replace('f.called=true;f.reply}','f.called=true;let mut reply=f.reply;reply[0]^=1;reply}')
helper+='\n#[cfg(kani)]\npub(super) fn NEL_first_relation()->bool{let d=['+','.join(['aspis_core::field::M31(kani::any())']*8)+'];let mut f=NEL_first::Frame{expected:d,reply:kani::any(),called:false};let r=NEL_first::threaded_first(&d,&mut f);r==f.reply[0] && f.called}\n'
append+=fappend
patch+=''.join(difflib.unified_diff(ff.splitlines(True),(ff+append+helper).splitlines(True),fromfile='a/'+forest,tofile='b/'+forest))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_lane_oracle.rs\n@@ -0,0 +1,'+str(len(fb.splitlines()))+' @@\n'+''.join('+'+line+'\n' for line in fb.splitlines())
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_first.rs\n@@ -0,0 +1,'+str(len(fbody.splitlines()))+' @@\n'+''.join('+'+line+'\n' for line in fbody.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_PAYMENT_FIELDS_CURRENT.json').write_text(json.dumps(dict(negative=negative,output_lane_reply_corruption=negative,source=path,source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),all_typed_inputs=True,actual_field_places=['transfer.recipient_commitment','transfer.change_commitment','withdrawal.change_commitment'],borrow_provenance=True,no_stub_verified=True,common_constructor='reuse CLOSED transfer_common/withdrawal_common; no reproof',classification='ruling y-prime inline borrowed field projections; native source expression identity and NEL_PaymentFieldCarriers supplied separately'),indent=1)+'\n')
