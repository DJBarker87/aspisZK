from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
s+='''
static mut NBO_MARK_CALLS:usize=0;
fn NBO_mark_none(obs:Observer,phase:Phase) {
 assert!(obs.is_none());
 match phase {Phase::Query(i)=>unsafe{assert_eq!(i,NBO_Q);},_=>panic!("wrong phase")}
 unsafe{NBO_MARK_CALLS+=1;}
}
'''
a=s.index('fn NBO_after_square_context() {');b=s.index('\n}',a)+2
case=s[a:b].replace('fn NBO_after_square_context()', 'fn NBO_after_square_checked_mark()')
case=case.replace('kani::cover!(next==0);','unsafe{assert_eq!(NBO_MARK_CALLS,1);}\n kani::cover!(next==0);')
s+='''#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBO_accumulate)]
#[kani::stub(crate::verifier::mark,NBO_mark_none)]
'''+case+'\n'
(E/'NBO_native.rs.txt').write_text(s)
