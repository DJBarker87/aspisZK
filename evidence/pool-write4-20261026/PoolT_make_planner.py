from pathlib import Path
import hashlib,json
B=Path('evidence/pool-write4-20261026')
s=Path('crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs').read_text()
v=Path('evidence/pool-write2-20261026/PoolV_tail/PoolV_lib.rs').read_text()
validate=v[v.index('fn validate_master('):v.index('\nfn PoolV_assembly')]
orig=s[s.index('pub fn plan_pool_v1_pair_forest_checkpoint_v1('):]
head=orig[:orig.index('    let mut lane_sequences')]
loop=orig[orig.index('    let mut lane_sequences'):orig.index('    if master.has_checkpoint')]
tail=orig[orig.index('    if master.has_checkpoint'):orig.index('    let checkpoint =')]
assembly=orig[orig.index('    let checkpoint ='):orig.index('\n}',orig.index('    let checkpoint ='))+2]
text='use aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\ntype Digest=[M31;8];\n'+validate+'\nfn digest_is_canonical(d:&Digest)->bool {d.iter().all(|x|x.0<2147483647)}\n'
text=text[:text.index('fn digest_is_canonical')]+s[s.index('fn digest_is_canonical('):s.index('fn digest_is_canonical(')+s[s.index('fn digest_is_canonical('):].index('\n}\n')+3].replace('P {','2147483647 {')+'\n'
text+='fn PoolT_loop(master:&PoolV1PairForestMasterV1,lanes:&[PoolV1PairForestLaneStateV1;8])->Result<[u64;8],PoolV1PairForestAccountErrorV1>{\n'+loop+'    Ok(lane_sequences)\n}\n'
text+='fn PoolT_tail(master:&PoolV1PairForestMasterV1,lane_sequences:[u64;8])->Result<u64,PoolV1PairForestAccountErrorV1>{\n'+tail+'    Ok(next_sequence)\n}\n'
text+='fn PoolT_assembly(master:&PoolV1PairForestMasterV1,lane_sequences:[u64;8],global_root:Digest,checkpoint_bump:u8,next_sequence:u64)->Result<PoolV1PairForestCheckpointPlanV1,PoolV1PairForestAccountErrorV1>{\n'+assembly+'\n'
text+=head.replace('pub fn plan_pool_v1_pair_forest_checkpoint_v1','fn PoolT_split')+'    let lane_sequences=PoolT_loop(master,lanes)?;\n    let next_sequence=PoolT_tail(master,lane_sequences)?;\n    PoolT_assembly(master,lane_sequences,global_root,checkpoint_bump,next_sequence)\n}\n'
p=Path('evidence/pool-write2-20261026/PoolV_pure/PoolV_lib.rs').read_text()
helpers=p[p.index('    fn arbitrary_master()'):p.index('    #[kani::proof]',p.index('    fn arbitrary_master()'))]
text+='#[cfg(kani)] mod PoolT_checks{use super::*;\n'+helpers+'''
#[kani::proof]
#[kani::unwind(80)]
fn PoolT_original_decomposition(){
 let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
 let original=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump);
 let split=PoolT_split(&m,&lanes,root,bump);
 assert!(original==split);
}
}
'''
(B/'PoolT_planner/PoolT_lib.rs').write_text(text)
(B/'PoolT_SOURCE.json').write_text(json.dumps({'original':{'path':'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs','sha256':hashlib.sha256(s.encode()).hexdigest()},'slices':{'head':head,'loop':loop,'tail':tail,'assembly':assembly},'scope':'Full original production planner compared against syntactically fissioned function on unrestricted original types; validate_master text reused from matched native PoolV slice'},indent=2)+'\n')
