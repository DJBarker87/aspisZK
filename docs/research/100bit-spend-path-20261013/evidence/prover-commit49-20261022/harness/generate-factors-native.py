from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
(E/'native/factor-iterations.rs').write_text('''
fn native_factor_step(factors:&[[[E;4];5];5],kind:usize,j:usize,d:usize,v:E)->E {
 let k=if kind<4 {kind-1}else{kind-2};
 v.mul(factors[k][d][(j>>(2*d))&3])
}
fn owner_factor_step(q:[E;5],d:usize,s:E)->E {s.mul(q[d])}
#[cfg(kani)] mod factor_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn raw_product_transition() {
  let raw:[u32;100]=kani::any();let factors:[[[E;4];5];5]=unsafe {core::mem::transmute(raw)};
  let kind:usize=kani::any();kani::assume(kind==1 || kind==2 || kind==3 || kind==5 || kind==6);
  let j:usize=kani::any();let d:usize=kani::any();kani::assume(j<1024 && d<5);
  let k=if kind<4 {kind-1}else{kind-2};
  let selected:[E;5]=core::array::from_fn(|d|factors[k][d][(j>>(2*d))&3]);
  let v=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_factor_step(&factors,kind,j,d,v);let ta=trace();
  reset(answers);let b=owner_factor_step(selected,d,v);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,1);
 }
}
''')
p=E/'native/lib.rs';s=p.read_text()
if 'factor-iterations.rs' not in s:s+='\ninclude!("factor-iterations.rs");\n'
p.write_text(s)
p=Path('crates/aspis-r1-cost-probe/src/weights.rs');s=p.read_text()
body='(0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))';assert body in s
(E/'pins/factor-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),literal=body,abstractions=['current legal factor-fold cursor and S2 kinds 1,2,3,5,6','full factor dimensions; output and every arithmetic operand/call compared','constructor factor values and raw method branches 0 and 4 are separate obligations']),indent=2)+'\n')
