from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'reconstruction-binding.rs' not in s:s+='\ninclude!("reconstruction-binding.rs");\n'
p.write_text(s)
(E/'native/reconstruction-binding.rs').write_text('''
// A CM reconstruction call records all three U64 arguments as operand markers.
// Its returned field handle is the final marker's universal answer. The actual
// three reductions/subtractions are proved in ReconstructC49, not stubbed true.
fn cm_reconstruct49(s:[u64;3])->E {
 call(16,E(s[0] as u32),E((s[0]>>32) as u32));
 call(16,E(s[1] as u32),E((s[1]>>32) as u32));
 call(16,E(s[2] as u32),E((s[2]>>32) as u32))
}
fn native_reconstruct49(s:[[u64;3];3])->(E,E) {
 let m0=cm_reconstruct49(s[0]);let m1=cm_reconstruct49(s[1]);let m2=cm_reconstruct49(s[2]);
 (m0.add(r_c(m1)),m2.sub(m0).sub(m1))
}
fn owner_reconstruct49(s:[[u64;3];3])->(E,E) {
 let m0=cm_reconstruct49(s[0]);let m1=cm_reconstruct49(s[1]);let m2=cm_reconstruct49(s[2]);
 let r=r_c(m1);let lo=m0.add(r);let t=m2.sub(m0);let hi=t.sub(m1);(lo,hi)
}
#[cfg(kani)] mod reconstruction_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(40)] fn complete_reconstruction_caller() {
  let s:[[u64;3];3]=kani::any();let answers=kani::any();
  reset(answers);let x=native_reconstruct49(s);let tx=trace();
  reset(answers);let y=owner_reconstruct49(s);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,13);
 }
}
''')
p=Path('crates/aspis-core/src/field.rs')
(E/'pins/reconstruction-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[482,503],binding='Complete QM31 reconstruction caller with verified CM reconstruction callees; every U64 argument recorded via low/high operand markers, then exact CM operation/operand order and both QM31 components. 13 trace entries are operand markers plus four CM operations, not a native arithmetic operation-count claim. ReconstructC49/ReconstructQ49 prove the concrete callee values and canonicality.'),indent=2)+'\n')
