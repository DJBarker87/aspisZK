from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2k-20261023';P=E/'S2K-native/src';f='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';src=(R/f).read_text();cuts={}
def cut(name,start,end,after=''):
 a=src.index(start,src.index(after) if after else 0);b=src.index(end,a);v=src[a:b];cuts[name]=dict(source=f,source_sha256=hashlib.sha256(src.encode()).hexdigest(),cut=v);return v
binding=cut('binding','    let common = statement.common();','\npub fn encode_pool_v1_pair_forest_terminal_result_v1','pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(')
head=cut('prefix','    let common = statement.common();','    match statement {','pub fn validate_pool_v1_pair_forest_terminal_statement_v1(')
helper=cut('public_common','fn statement_public_common(','\npub fn validate_pool_v1_pair_forest_terminal_statement_v1(')
lane=cut('lane','    let (pool, deployment, anchor_sequence, anchor, nullifier, _) =','    let mut late_bytes =','pub fn validate_pool_v1_pair_forest_terminal_statement_v1(')
s='fn binding_tail(statement:&PoolV1PairForestTerminalStatementV1,result:&PoolV1PairForestTerminalResultV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {\n'+binding
s+='fn binding_prefix(statement:&PoolV1PairForestTerminalStatementV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {\n'+head+'    Ok(())\n}\n'
s+=helper+'\nfn lane_binding(statement:&PoolV1PairForestTerminalStatementV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {\n    let common=statement.common();\n'+lane+'    Ok(())\n}\n'
s+='''#[kani::proof]
#[kani::unwind(34)]
fn S2K_binding_tail() {
    let statement=statement::statement();let result=construct(&statement);
    assert_eq!(binding_tail(&statement,&result),Ok(()));
    kani::cover!(statement.transition_kind()==PoolV1TransitionKind::PrivateTransfer);
    kani::cover!(statement.transition_kind()==PoolV1TransitionKind::Withdrawal);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_binding_prefix() {
    let statement=statement::statement();let c=statement.common();
    let expected=if c.master_account==[0;32] || c.checkpoint_account==[0;32] || c.selected_lane_account==[0;32] {
        Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)
    } else if c.output_lane>=8 {Err(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane)} else {Ok(())};
    assert_eq!(binding_prefix(&statement),expected);
    kani::cover!(expected.is_ok());kani::cover!(expected.is_err());
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_lane_binding() {
    let statement=statement::statement();let result=construct(&statement);
    if lane_binding(&statement).is_ok() {
        assert_eq!(pool_v1_pair_forest_output_lane_v1(&result.nullifier),Ok(result.output_lane));
    }
    kani::cover!(lane_binding(&statement).is_ok());
}
'''
(P/'S2K_admission.rs').write_text(s);(E/'admission-cuts.json').write_text(json.dumps(cuts,indent=2)+'\n')
p=P/'lib.rs';s=p.read_text();line='include!("S2K_admission.rs");\n';assert line not in s;p.write_text(s+'\n'+line)
