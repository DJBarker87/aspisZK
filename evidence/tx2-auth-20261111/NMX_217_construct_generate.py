from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;frozen=Path('programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();s=frozen[frozen.index('    Ok(Box::new(PoolV1PairForestLaneStateV1 {'):];s=s[:s.index('\n}')]
s=s.replace('Ok(Box::new','Box::new',1);assert s.endswith('}))');s=s[:-1]
actual=s.replace('bytes[72]','input.bump').replace('bytes[5]','input.lane_id').replace('        master,','        master: input.master,').replace('            next_leaf_index,','            next_leaf_index: input.tree.next_leaf_index,').replace('            root,','            root: input.tree.root,').replace('            frontier,','            frontier: input.tree.frontier,')
stubs='\n'.join(dict.fromkeys(x for x in (E/'NMX_217_iteration.rs').read_text().splitlines() if x.startswith('#[kani::stub(')))
fragment='''
#[kani::modifies()]
#[kani::ensures(|r:&bool| *r != INVERSE)]
fn NMX_construct(input:&PoolV1PairForestLaneStateV1)->bool{
 let output =
'''+actual+''';
 *output==*input
}
#[kani::proof_for_contract(NMX_construct)]
'''+stubs+'''
#[kani::unwind(34)]
fn NMX_construct_contract(){
 let input=PoolV1PairForestLaneStateV1{bump:kani::any(),master:kani::any(),lane_id:kani::any(),tree:IncrementalMerkleTreeV1{next_leaf_index:kani::any(),root:kani::any(),frontier:kani::any()}};
 let _=NMX_construct(&input);
}
'''
p=E/'NMX_217_iteration.rs';old=p.read_text();assert 'fn NMX_construct(' not in old;p.write_text(old+fragment)
(E/'NMX_217_CONSTRUCT_CUT.json').write_text(json.dumps({'source':'programs/r1-cost-probe/src/r1_pool_adapter.rs','segment':'accepted final guard to Box return, no guard bundled','constructor':actual,'substitutions':{'bytes[72]':'input.bump','bytes[5]':'input.lane_id','master':'input.master','next_leaf_index':'input.tree.next_leaf_index','root':'input.tree.root','frontier':'input.tree.frontier'},'returned_payload':'deep equality of all fields, not a selected projection','frame':'no existing input mutated; allocation is owned fresh object; silent abort interpreted by std item'},indent=2)+'\n')
