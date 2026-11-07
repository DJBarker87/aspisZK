from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;frozen=Path('programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();a=frozen.index('    if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]');s=frozen[a:];s=s[:s.index('\n}')]
actual=s.replace('bytes[72]','bump').replace('bytes[5]','lane_id')
stubs='\n'.join(dict.fromkeys(x for x in (E/'NMX_217_iteration.rs').read_text().splitlines() if x.startswith('#[kani::stub(')))
fragment='''
fn NMX_lane_observe(a:&PoolV1PairForestLaneStateV1,j:usize)->u64{
 match j{0=>a.bump as u64,1=>a.lane_id as u64,2=>a.tree.next_leaf_index,
  3..=34=>a.master[j-3] as u64,35..=42=>a.tree.root[j-35].0 as u64,
  _=>a.tree.frontier[(j-43)/8][(j-43)%8].0 as u64}
}
fn NMX_final_post(r:bool)->bool{r != INVERSE}
#[kani::requires(j<203)]
#[kani::modifies()]
#[kani::ensures(|r:&bool| NMX_final_post(*r))]
fn NMX_final(bump:u8,master:[u8;32],lane_id:u8,next_leaf_index:u64,
 root:[M31;8],frontier:[[M31;8];20],j:usize)->bool{
 use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
 let actual:Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>=(||{
'''+actual+'''
 })();
 let row=root.map(|x|x.0);
 let rejected=next_leaf_index==0&&!R::eq_digest(&row,&R::EMPTY[20]);
 let expected=match j{0=>bump as u64,1=>lane_id as u64,2=>next_leaf_index,
 3..=34=>master[j-3] as u64,35..=42=>root[j-35].0 as u64,
 _=>frontier[(j-43)/8][(j-43)%8].0 as u64};
 match actual{Err(e)=>rejected&&matches!(e,ProgramError::InvalidAccountData),
 Ok(a)=>!rejected&&NMX_lane_observe(&a,j)==expected}
}
#[kani::proof_for_contract(NMX_final)]
'''+stubs+'''
#[kani::unwind(34)]
fn NMX_final_contract(){let j:usize=kani::any();kani::assume(j<203);let _=NMX_final(kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),j);}
'''
p=E/'NMX_217_iteration.rs';old=p.read_text();assert 'fn NMX_final(' not in old;p.write_text(old+fragment)
(E/'NMX_217_FINAL_CUT.json').write_text(json.dumps({'source':'programs/r1-cost-probe/src/r1_pool_adapter.rs','source_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_sha256':hashlib.sha256(frozen.encode()).hexdigest(),'segment':'after frontier loop through returned Box','substitutions':{'bytes[72]':'bump','bytes[5]':'lane_id'},'observations':203,'carrier':'all M31 u32 representations; arbitrary typed frontier; no decoder-loop unwinding','source_segment_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2)+'\n')
