from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;p=Path('crates/aspis-r1-cost-probe/src/host_sumcheck.rs');s=p.read_text()
a=s.index('                    let shifted = if k == 0');b=s.index('\n                }',a);body=s[a:b]
text='''#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct M31(u32);
impl M31 {
 const ZERO:Self=M31(0);
 fn mul(self,y:Self)->Self {M31(call(2,E(self.0),E(y.0)).0)}
 fn sub(self,y:Self)->Self {M31(call(3,E(self.0),E(y.0)).0)}
}
fn native_basis_step(mut basis:[M31;28],k:usize,j:usize)->[M31;28] {
'''+body+'''
 basis
}
fn predecessor_ref(basis:[M31;28],k:usize)->M31 {if k==0 {M31::ZERO} else {basis[k-1]}}
fn owner_basis_step(mut basis:[M31;28],k:usize,j:usize)->[M31;28] {
 let shifted=predecessor_ref(basis,k);
 let next=shifted.sub(basis[k].mul(M31(j as u32)));
 basis[k]=next;basis
}
#[cfg(kani)] mod interpolation_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn basis_coefficient_step() {
  let raw:[u32;28]=kani::any();let basis=raw.map(M31);
  let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<28 && j<28);
  let answers=kani::any();
  reset(answers);let actual=native_basis_step(basis,k,j);let ta=trace();
  reset(answers);let expected=owner_basis_step(basis,k,j);let tb=trace();
  assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
'''
(H/'interpolate-iterations.rs').write_text(text)
(H/'interpolate-spans.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='One arbitrary legal descending coefficient update, with every arithmetic operand and return traced; native body is verbatim.'),indent=2)+'\n')
