"""One actual frozen pure-function contract at a time, with explicit empty frame."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
case,control=sys.argv[1:];assert control in {'positive','negative'}
root='crates/aspis-statement/src/pool_v1/'
terminal=root+'pair_forest_terminal.rs';payment=root+'payment_relation.rs'
get=lambda p:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
base,hook=oracle_parts()
kmx='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
'''
extra='';newfiles={}
if case=='common':
 path=terminal;needle='    pub fn common(&self) -> &PoolV1PairForestTerminalCommonV1 {'
 expr='core::ptr::eq(*r, match self {Self::PrivateTransfer{common,..}|Self::Withdrawal{common,..}=>common})'
 harness='#[kani::proof_for_contract(PoolV1PairForestTerminalStatementV1::common)]\n'+kmx+'fn frame_common(){let s=NEE_statement();let _=s.common();}\n'
 owner='NEE_oracle';target='frame_common'
elif case=='parts':
 path=terminal;needle='fn statement_public_common('
 fields='(public.pool,public.deployment_domain,public.anchor_sequence,public.anchor_root,public.nullifier,public.asset_id)'
 expr='*r == match statement {PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>'+fields+',PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>'+fields+'}'
 harness='#[kani::proof_for_contract(statement_public_common)]\n'+kmx+'fn frame_parts(){let s=NEE_statement();let _=statement_public_common(&s);}\n'
 owner='NEE_oracle';target='frame_parts'
else:
 path=payment;owner='NEE_payment_frames';target='frame_'+case
 # Constructors use exactly the same typed arbitrary records as the parent.
 utilities=base[base.index('fn NEE_digest()'):base.index('fn NEE_common()')]
 utilities+='''
fn t()->PoolV1PrivateTransferPublicV1 {PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NEE_digest(),nullifier:NEE_digest(),asset_id:M31(kani::any()),recipient_commitment:NEE_digest(),change_commitment:NEE_digest()}}
fn w()->PoolV1WithdrawalPublicV1 {PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NEE_digest(),nullifier:NEE_digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:NEE_digest()}}
pub(super) fn canonical(d:&Digest)->bool {d[0].0<P&&d[1].0<P&&d[2].0<P&&d[3].0<P&&d[4].0<P&&d[5].0<P&&d[6].0<P&&d[7].0<P}
pub(super) fn common_spec(c:&CommonPublicV1)->Result<(),PoolV1PaymentStatementFormatError> {
 if c.pool==[0;32]||c.deployment_domain==[0;32]{Err(PoolV1PaymentStatementFormatError::ZeroRequiredBinding)}
 else if c.anchor_sequence>POOL_V1_LEAF_CAPACITY{Err(PoolV1PaymentStatementFormatError::InvalidAnchorSequence)}
 else if !canonical(&c.anchor_root)||!canonical(&c.nullifier){Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest)}
 else if c.asset_id.0>=P{Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId)}else{Ok(())}
}
pub(super) fn t_spec(p:&PoolV1PrivateTransferPublicV1)->Result<(),PoolV1PaymentStatementFormatError> {
 common_spec(&CommonPublicV1{pool:p.pool,deployment_domain:p.deployment_domain,anchor_sequence:p.anchor_sequence,anchor_root:p.anchor_root,nullifier:p.nullifier,asset_id:p.asset_id})?;
 if !canonical(&p.recipient_commitment)||!canonical(&p.change_commitment){Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest)}else{Ok(())}
}
pub(super) fn w_spec(p:&PoolV1WithdrawalPublicV1)->Result<(),PoolV1PaymentStatementFormatError> {
 common_spec(&CommonPublicV1{pool:p.pool,deployment_domain:p.deployment_domain,anchor_sequence:p.anchor_sequence,anchor_root:p.anchor_root,nullifier:p.nullifier,asset_id:p.asset_id})?;
 if p.amount==0||p.amount>=VALUE_LIMIT{Err(PoolV1PaymentStatementFormatError::InvalidWithdrawalAmount)}
 else if p.destination_token_account==[0;32]{Err(PoolV1PaymentStatementFormatError::InvalidDestination)}
 else if !canonical(&p.change_commitment){Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest)}else{Ok(())}
}
'''
 if case in {'transfer_common','withdrawal_common'}:
  needle='fn '+case+'(';expr='r.pool==public.pool && r.deployment_domain==public.deployment_domain && r.anchor_sequence==public.anchor_sequence && r.anchor_root==public.anchor_root && r.nullifier==public.nullifier && r.asset_id==public.asset_id'
  call='let p='+('t' if case=='transfer_common' else 'w')+'();let _='+case+'(&p);'
 elif case=='canonical':
  needle='fn digest_is_canonical(';expr='*r == NEE_payment_frames::canonical(digest)';call='let d=NEE_digest();let _=digest_is_canonical(&d);'
 elif case=='validate_common':
  needle='fn validate_common(';expr='*r == NEE_payment_frames::common_spec(&common)';call='let p=t();let c=CommonPublicV1{pool:p.pool,deployment_domain:p.deployment_domain,anchor_sequence:p.anchor_sequence,anchor_root:p.anchor_root,nullifier:p.nullifier,asset_id:p.asset_id};let _=validate_common(c);'
 elif case in {'validate_transfer','validate_withdrawal'}:
  fn='validate_pool_v1_'+('private_transfer' if case=='validate_transfer' else 'withdrawal')+'_public_v1'
  needle='pub fn '+fn+'(';expr='*r == NEE_payment_frames::'+('t' if case=='validate_transfer' else 'w')+'_spec(public)';call='let p='+('t' if case=='validate_transfer' else 'w')+'();let _='+fn+'(&p);'
 else:raise SystemExit('unknown case '+case)
 fn=needle.split('fn ')[1].split('(')[0]
 harness='use super::*;\n'+utilities+'\n#[kani::proof_for_contract('+fn+')]\n'+kmx+'fn '+target+'(){'+call+'}\n'
 newfiles[root+'NEE_payment_frames.rs']=harness
 # Hook is part of our reversible contract patch, so each case remains isolated.
 extra='\n#[cfg(kani)]\n#[path="NEE_payment_frames.rs"]\nmod NEE_payment_frames;\n'
expr=('!('+expr+')') if control=='negative' else expr
indent='    ' if case=='common' else ''
attrs=indent+'#[cfg_attr(kani,kani::modifies())]\n'+indent+'#[cfg_attr(kani,kani::ensures(|r| '+expr+'))]\n'
frozen=get(path);assert frozen.count(needle)==1
# Preserve the existing four-space indentation on a method.
changed=frozen.replace(needle,attrs+needle) if case!='common' else frozen.replace(needle,attrs+needle)
assert changed.replace(attrs,'')==frozen
changed+=extra
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
for name,body in newfiles.items():
 patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
body=base+(harness if case in {'common','parts'} else '')
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/'+root+'NEE_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())+hook)
(E/'NEE_CONTRACT_ERASURE.json').write_text(json.dumps(dict(case=case,control=control,actual_frozen_body_unchanged=True,sha256=hashlib.sha256(frozen.encode()).hexdigest(),contract_patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),harness='pool_v1::'+('pair_forest_terminal' if case in {'common','parts'} else 'payment_relation')+'::'+owner+'::'+target),indent=1)+'\n')
print(json.loads((E/'NEE_CONTRACT_ERASURE.json').read_text())['harness'])
