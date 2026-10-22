from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
s=Path('crates/aspis-r1-cost-probe/src/sim.rs').read_text()
p=Path('crates/aspis-r1-cost-probe/src/prover.rs').read_text()
expr='s.add(gp[l].mul(coefficients[l][j]))'
assert s.count(expr)==1
start=p.index('        else {h[0].add(alpha.mul(');end=p.index('\n    }).collect()',start)
fold=p[start:end].removeprefix('        else {').removesuffix('}')
owner=H.parent/'opening-owner/lib.rs';o=owner.read_text()
assert 'sum.add(powers[i].mul(coefficients[i]))' in o
assert 'h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))' in o
text='''// Literal shipped expressions at the arbitrary current source iteration.
struct Column {index:usize,value:E}
impl core::ops::Index<usize> for Column {
 type Output=E;
 fn index(&self,i:usize)->&E {assert_eq!(i,self.index);&self.value}
}
fn native_mix(gp:&[E;29],coefficients:&[Column;29],j:usize,l:usize,s:E)->E {
 '''+expr+'''
}
fn owner_mix(powers:[E;29],coefficients:[E;29],i:usize,sum:E)->E {
 sum.add(powers[i].mul(coefficients[i]))
}
fn native_fold(h:[E;4],alpha:E)->E {
 '''+fold+'''
}
fn owner_fold(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}
#[cfg(kani)] mod opening_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(32)]
 fn mix_iteration() {
  let raw:[u32;29]=kani::any();let gp=raw.map(E);
  let raw:[u32;29]=kani::any();let coefficients=raw.map(E);
  let j:usize=kani::any();let l:usize=kani::any();kani::assume(j<1024 && l<29);
  let columns=coefficients.map(|value|Column{index:j,value});
  let sum=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_mix(&gp,&columns,j,l,sum);let ta=trace();
  reset(answers);let b=owner_mix(gp,coefficients,l,sum);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
 #[kani::proof] #[kani::unwind(10)]
 fn fold_primal_cell() {
  let raw:[u32;4]=kani::any();let h=raw.map(E);let alpha=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_fold(h,alpha);let ta=trace();
  reset(answers);let b=owner_fold(h,alpha);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,6);
 }
}
'''
(H/'opening-iterations.rs').write_text(text)
(H/'opening-spans.json').write_text(json.dumps(dict(source_sha256={'sim.rs':hashlib.sha256(s.encode()).hexdigest(),'prover.rs':hashlib.sha256(p.encode()).hexdigest()},expressions={'mix':expr,'fold':fold},projection='Column is an arbitrary current coefficient cell; Index asserts the exact requested j, which is arbitrary below 1024. No value is assumed for unaccessed cells.',owner_sha256=hashlib.sha256(owner.read_bytes()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest()),indent=2)+'\n')
