"""Constructive cfg(kani)-only generators; every frozen record field is arbitrary."""
import subprocess,re
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def additions():
 def frozen(p):return subprocess.check_output(['git','show',REV+':'+p],text=True)
 out={}
 n='crates/aspis-core/src/lib.rs';out[n]=frozen(n)+'\n#[cfg(kani)]\n#[path="NDM_arbitrary.rs"]\nmod NDM_arbitrary;\n'
 out['crates/aspis-core/src/NDM_arbitrary.rs']='impl kani::Arbitrary for crate::field::M31 {fn any()->Self {Self(kani::any())}}\n'
 n='crates/aspis-statement/src/pool_v1/mod.rs';out[n]=frozen(n)+'\n#[cfg(kani)]\n#[path="NDM_arbitrary.rs"]\nmod NDM_arbitrary;\n'
 structs=[
 ('pair_forest_terminal','PoolV1PairForestTerminalCommonV1','master_account checkpoint_account selected_lane_account output_lane checkpoint_sequence historical_global_anchor lane_transition'),
 ('pair_tree_profile','PoolV1PairLatePublicStatementV1','live_snapshot candidate_afterstate'),
 ('pair_tree_profile','PoolV1PairLiveSnapshotV1','pool deployment_domain sequence next_pair_index current_root frontier'),
 ('pair_terminal','PoolV1PairVerifiedAfterstateV1','next_pair_index next_root next_frontier'),
 ('payment_relation','PoolV1PrivateTransferPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id recipient_commitment change_commitment'),
 ('payment_relation','PoolV1WithdrawalPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id amount destination_token_account change_commitment')]
 s=''
 for module,name,fields in structs:
  s+='impl kani::Arbitrary for super::'+module+'::'+name+' { fn any()->Self {Self {'+','.join(f+':kani::any()' for f in fields.split())+'}}}\n'
 s+='impl kani::Arbitrary for super::pair_forest_terminal::PoolV1PairForestTerminalStatementV1 {fn any()->Self {if kani::any(){Self::PrivateTransfer{common:kani::any(),public:kani::any()}} else {Self::Withdrawal{common:kani::any(),public:kani::any()}}}}\n'
 errors=[('pair_forest_terminal','PoolV1PairForestTerminalFormatErrorV1'),('payment_relation','PoolV1PaymentStatementFormatError'),('pair_tree_profile','PoolV1PairLatePublicStatementErrorV1'),('pair_tree_profile','PoolV1PairLiveSnapshotErrorV1'),('pair_terminal','PoolV1PairVerifierTransportErrorV1'),('pair_forest_accounts','PoolV1PairForestAccountErrorV1'),('incremental_merkle','PoolV1TreeError')]
 for module,name in errors:
  text=frozen('crates/aspis-statement/src/pool_v1/'+module+'.rs');part=text.split('pub enum '+name+' {',1)[1].split('}',1)[0]
  variants=[]
  for line in part.splitlines():
   m=re.fullmatch(r'\s*(\w+)(?:\(([\w:]+)\))?,\s*',line)
   if m:variants.append('Self::'+m[1]+('(kani::any())' if m[2] else ''))
  assert variants
  s+='impl kani::Arbitrary for super::'+module+'::'+name+' {fn any()->Self {match kani::any::<u8>() % '+str(len(variants))+' {'+','.join((str(i) if i<len(variants)-1 else '_')+'=>'+v for i,v in enumerate(variants))+'}}}\n'
 out['crates/aspis-statement/src/pool_v1/NDM_arbitrary.rs']=s
 return out
