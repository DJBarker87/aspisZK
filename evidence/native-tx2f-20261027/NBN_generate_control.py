from pathlib import Path
import re,json,subprocess,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files={p:subprocess.check_output(['git','show',REV+':'+p],text=True) for p in [
'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs',
'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs',
'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',
'crates/aspis-statement/src/pool_v1/pair_terminal.rs',
'crates/aspis-statement/src/pool_v1/payment_relation.rs',
'crates/aspis-statement/src/pool_v1/incremental_merkle.rs']}
alltext='\n'.join(files.values())
# Exact child error sums, including every nested constructor.
def variants(name):
 b=re.search(r'pub enum '+name+r'\s*\{([^}]+)\}',alltext).group(1)
 b=re.sub(r'//[^\n]*','',b)
 return re.findall(r'(\w+)(?:\((\w+)\))?\s*,',b)
needed=['PoolV1PaymentStatementFormatError','PoolV1PairForestAccountErrorV1','PoolV1PairLatePublicStatementErrorV1']
seen=set();gens=[]
def gen(name):
 if name in seen:return
 seen.add(name);vs=variants(name)
 for _,ty in vs:
  if ty:gen(ty)
 arms=[]
 for i,(v,ty) in enumerate(vs):
  tag=str(i) if i<len(vs)-1 else '_'
  val='crate::pool_v1::'+name+'::'+v+(f'(NBN_any_{ty}())' if ty else '')
  arms.append(tag+'=>'+val)
 gens.append(f'fn NBN_any_{name}()->crate::pool_v1::{name} {{ match kani::any::<u8>() {{'+','.join(arms)+'} }\n')
for n in needed:gen(n)
body=files['crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs']
a=body.index('pub fn validate_pool_v1_pair_forest_terminal_statement_v1(');b=body.index('\npub fn encode_pool_v1_pair_forest_terminal_statement_v1',a)
cut=body[a:b].replace('pub fn validate_pool_v1_pair_forest_terminal_statement_v1(','fn NBN_validator_cut(')
cut=cut.replace('    statement: &PoolV1PairForestTerminalStatementV1,','    statement: &PoolV1PairForestTerminalStatementV1,\n    payment: Result<[u8;216],PoolV1PaymentStatementFormatError>,\n    lane: Result<u8,PoolV1PairForestAccountErrorV1>,\n    late: Result<(),PoolV1PairLatePublicStatementErrorV1>,')
x=cut.index('    match statement {');y=cut.index('    let (pool,',x)
cut=cut[:x]+'''    payment.map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
'''+cut[y:]
cut=cut.replace('pool_v1_pair_forest_output_lane_v1(&nullifier)','lane')
x=cut.index('    let mut late_bytes');y=cut.index('    Ok(())',x)
cut=cut[:x]+'''    late.map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)?;
'''+cut[y:]
# Generator emits explicit arbitrary field constructors, never a protocol loop.
digest='['+','.join(['M31(kani::any())']*8)+']'
frontier='['+','.join(['NBN_digest()']*20)+']'
common='''PoolV1PairForestTerminalCommonV1{master_account:kani::any(),checkpoint_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),checkpoint_sequence:kani::any(),historical_global_anchor:NBN_digest(),lane_transition:PoolV1PairLatePublicStatementV1{live_snapshot:super::super::PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:NBN_digest(),frontier:NBN_frontier()},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:NBN_digest(),next_frontier:NBN_frontier()}}}'''
fields='pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NBN_digest(),nullifier:NBN_digest(),asset_id:M31(kani::any()),change_commitment:NBN_digest()'
s='#![allow(non_snake_case,unused_variables)]\nuse super::*;\n'+''.join(gens)
s+=f'fn NBN_digest()->Digest {{{digest}}}\nfn NBN_frontier()->[Digest;20] {{{frontier}}}\n'
s+=f'fn NBN_common()->PoolV1PairForestTerminalCommonV1 {{{common}}}\n'
s+=f'''fn NBN_statement()->PoolV1PairForestTerminalStatementV1 {{
 if kani::any::<bool>() {{PoolV1PairForestTerminalStatementV1::PrivateTransfer{{common:NBN_common(),public:PoolV1PrivateTransferPublicV1{{{fields},recipient_commitment:NBN_digest()}}}}}}
 else {{PoolV1PairForestTerminalStatementV1::Withdrawal{{common:NBN_common(),public:PoolV1WithdrawalPublicV1{{{fields},amount:kani::any(),destination_token_account:kani::any()}}}}}}
}}
'''+cut
s+='''
fn NBN_expected(s:&PoolV1PairForestTerminalStatementV1,pay:Result<[u8;216],PoolV1PaymentStatementFormatError>,lane:Result<u8,PoolV1PairForestAccountErrorV1>,late:Result<(),PoolV1PairLatePublicStatementErrorV1>)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{
 let c=s.common(); let (pool,domain,seq,anchor,_,_)=statement_public_common(s);
 if c.master_account==[0;32]||c.checkpoint_account==[0;32]||c.selected_lane_account==[0;32] {Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}
 else if c.output_lane>=8 {Err(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane)}
 else {match pay {
  Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e)),
  Ok(_)=>{
   if pool!=c.master_account {Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch)}
   else if domain!=c.lane_transition.live_snapshot.deployment_domain {Err(PoolV1PairForestTerminalFormatErrorV1::DeploymentBindingMismatch)}
   else if c.lane_transition.live_snapshot.pool!=c.master_account {Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch)}
   else if seq!=c.checkpoint_sequence {Err(PoolV1PairForestTerminalFormatErrorV1::CheckpointBindingMismatch)}
   else if anchor!=c.historical_global_anchor {Err(PoolV1PairForestTerminalFormatErrorV1::HistoricalAnchorMismatch)}
   else {match lane {
    Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::Account(e)),
    Ok(l)=>if l!=c.output_lane {Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch)} else {match late {Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition(e)),Ok(())=>Ok(())}}
   }}
  }
 }}
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_validator_control(){
 let s=NBN_statement();
 let pay=if kani::any::<bool>() {Ok([0;216])} else {Err(NBN_any_PoolV1PaymentStatementFormatError())};
 let lane=if kani::any::<bool>() {Ok(kani::any())} else {Err(NBN_any_PoolV1PairForestAccountErrorV1())};
 let late=if kani::any::<bool>() {Ok(())} else {Err(NBN_any_PoolV1PairLatePublicStatementErrorV1())};
 assert_eq!(NBN_validator_cut(&s,pay,lane,late),NBN_expected(&s,pay,lane,late));
}
'''
(E/'NBN_more.rs.txt').write_text(s)
(E/'NBN_CONTROL_EXTRACTION.json').write_text(json.dumps({'frozen_revision':REV,'source':'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','source_body':'validate_pool_v1_pair_forest_terminal_statement_v1','child_cuts':['same-variant payment Result','same-nullifier output-lane Result','same-transition late Result'],'stubs':[],'error_generators':{n:variants(n) for n in sorted(seen)},'unwind':1881,'scope':'ordered caller control cut, not whole native child codecs'},indent=2)+'\n')
