from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'libra-binding.rs' not in s:s+='\ninclude!("libra-binding.rs");\n'
p.write_text(s)
(E/'native/libra-binding.rs').write_text('''
fn power_call(x:E,n:u64)->E {assert!(n<=255);call(10,x,E(n as u32))}
fn native_libra(extra:[E;2],j:usize)->E {
 if j<56 {power_call(extra[j/28],(j%28) as u64)} else {E(0)}
}
fn owner_libra(extra:[E;2],j:usize)->E {
 if j<56 {power_call(extra[j/28],((j%28) as u8) as u64)} else {E(0)}
}
fn lift_c(x:E)->E {call(11,x,E(0))}
fn lift_q(x:E)->E {call(12,x,E(0))}
fn native_half()->E {lift_q(lift_c(inv_m(E(2))))}
fn owner_half()->E {let m=inv_m(E(2));let c=lift_c(m);lift_q(c)}
#[cfg(kani)] mod libra_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(20)] fn libra_half_callers() {
  let extra=[E(kani::any()),E(kani::any())];let j:usize=kani::any();let answers=kani::any();
  reset(answers);let x=native_libra(extra,j);let tx=trace();
  reset(answers);let y=owner_libra(extra,j);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,if j<56 {1}else{0});
  reset(answers);let x=native_half();let tx=trace();
  reset(answers);let y=owner_half();let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,3);
 }
}
''')
paths=['crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/sim.rs']
(E/'pins/libra-half-native-spans.json').write_text(json.dumps(dict(sources={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},binding='Complete raw kind-4 j dispatch, index/division/exponent narrowing and pow call; complete half embedding chain. Full power and fixed M31 inverse are independently checked.',scope='Universal j and field handles; full operation/operand traces, no value/model premise in the gate.'),indent=2)+'\n')
