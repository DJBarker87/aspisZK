from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
p=E/'NHG_public_plan.rs.txt';s=p.read_text();sem=(E/'NHG_semantic.rs.txt').read_text();init=sem[sem.index(' let p=PoolV1'):sem.index(' let result=public.semantic()')]
s+='''
// The two by-value snapshot loads, with one arbitrary observed live word.
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_snapshot_word(){
'''+init+'''
 let p=public.semantic();
 let source = p.transition.live_snapshot;
 let after = p.transition.candidate_afterstate;
 let kind:u8=kani::any();kani::assume(kind<4);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);
 if cfg!(NHG_invert){kani::assume(kind==1);}
 let got=match kind{0=>source.next_pair_index,1=>source.frontier[row][word].0 as u64,2=>after.next_root[word].0 as u64,_=>after.next_frontier[row][word].0 as u64};
 let expected=match kind{0=>t.live_snapshot.next_pair_index,1=>t.live_snapshot.frontier[row][word].0 as u64,2=>t.candidate_afterstate.next_root[word].0 as u64,_=>t.candidate_afterstate.next_frontier[row][word].0 as u64};
 assert_eq!(got,expected^if cfg!(NHG_invert){1}else{0});
}
''';p.write_text(s)
m=json.loads((E/'NHG_OVERLAY.json').read_text());(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/v).read_bytes()).hexdigest()for n,v in m.items()},indent=1))
