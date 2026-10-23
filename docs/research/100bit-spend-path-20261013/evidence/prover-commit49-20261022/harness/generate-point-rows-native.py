from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'point-rows-binding.rs' not in s:s+='\ninclude!("point-rows-binding.rs");\n'
p.write_text(s)
(E/'native/point-rows-binding.rs').write_text('''
const TAU49:[usize;5]=[3,4,2,0,1];
fn native_point_rows_step(mut factors:[[[E;4];5];5],points:[[E;10];3],k:usize,d:usize)->[[[E;4];5];5] {
 let a=points[k][9-2*TAU49[d]];let b=points[k][8-2*TAU49[d]];
 factors[k][d]=[E::ONE.sub(a).mul(E::ONE.sub(b)),a.mul(E::ONE.sub(b)),E::ONE.sub(a).mul(b),a.mul(b)];factors
}
fn owner_point_rows_step(p:[E;10],mut out:[[E;4];5],d:usize)->[[E;4];5] {
 let t=TAU49[d];let a=p[9-2*t];let b=p[8-2*t];
 out[d]=owner_point_factor(a,b);out
}
#[cfg(kani)] mod point_rows_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(128)] fn point_row_transition() {
  let factors:[[[E;4];5];5]=unsafe{core::mem::transmute(kani::any::<[u32;100]>())};
  let points:[[E;10];3]=unsafe{core::mem::transmute(kani::any::<[u32;30]>())};
  let k:usize=kani::any();let d:usize=kani::any();kani::assume(k<3 && d<5);let answers=kani::any();
  reset(answers);let x=native_point_rows_step(factors,points,k,d);let tx=trace();
  reset(answers);let row=owner_point_rows_step(points[k],factors[k],d);let ty=trace();
  let mut y=factors;y[k]=row;assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,8);
 }
}
''')
p=Path('crates/aspis-r1-cost-probe/src/weights.rs')
(E/'pins/point-rows-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),transport_source='crates/aspis-r1-cost-probe/src/transport.rs',transport_sha256=hashlib.sha256(Path('crates/aspis-r1-cost-probe/src/transport.rs').read_bytes()).hexdigest(),binding='Actual point-factor row write for arbitrary entire initialized factors matrix and points, all legal k/d, exact operation/operand trace and all context preserved. Heap initialization safety gate from part48 is retained separately.'),indent=2)+'\n')
