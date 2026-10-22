from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;p=Path('crates/aspis-r1-cost-probe/src/host_semantic.rs');s=p.read_text()
expr='v.mul(if s==0 {a}else{b}).add(c)';assert s.count(expr)==1
text='''// Native closure at its current reverse-iterator cursor.
fn native_extra_step(coefficients:&[E;1024],s:usize,j:usize,a:E,b:E,v:E)->E {
 let c=coefficients[s*28+j];
 '''+expr+'''
}
fn owner_extra_step(q:[E;1024],offset:usize,j:usize,x:E,sum:E)->E {sum.mul(x).add(q[offset+j])}
#[cfg(kani)] mod extra_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn horner_transition() {
  let raw:[u32;1024]=kani::any();let q:[E;1024]=unsafe {core::mem::transmute(raw)};
  let s:usize=kani::any();let j:usize=kani::any();kani::assume(s<2 && j<28);
  let a=E(kani::any());let b=E(kani::any());let v=E(kani::any());let answers=kani::any();
  reset(answers);let actual=native_extra_step(&q,s,j,a,b,v);let ta=trace();
  reset(answers);let expected=owner_extra_step(q,s*28,j,if s==0 {a}else{b},v);let tb=trace();
  assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
'''
(H/'extra-iterations.rs').write_text(text)
(H/'extra-spans.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),expression=expr,generated_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Arbitrary side and legal reverse-iterator position; fixed 1024 coefficients; complete primitive trace. The helper field is parametric, and its actual QM31 contracts are proved separately.'),indent=2)+'\n')
