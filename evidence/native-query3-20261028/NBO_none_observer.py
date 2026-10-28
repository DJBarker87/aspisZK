from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
s+='''
#[kani::proof]
fn NBO_none_mark_native() {
 let i:usize=kani::any();kani::assume(i<10);
 mark(None,Phase::Query(i));
 kani::cover!(i==0);kani::cover!(i==9);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
