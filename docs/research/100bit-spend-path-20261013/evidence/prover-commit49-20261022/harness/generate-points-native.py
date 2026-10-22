from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
(E/'native/points-iterations.rs').write_text('''
fn native_successor_step(z:&[E;10],mut successor:[E;10],coordinate:usize,mut carry:E)->([E;10],E) {
 let bit=z[coordinate];
 let bit_and_carry=bit.mul(carry);
 successor[coordinate]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
 carry=bit_and_carry;(successor,carry)
}
fn owner_successor_step(p:[E;10],mut out:[E;10],left:u8,carry:E)->([E;10],E) {
 let coordinate=(left-1) as usize;
 let bit=p[coordinate];let bc=bit.mul(carry);
 out[coordinate]=bit.add(carry).sub(bc.add(bc));(out,bc)
}
fn native_absorption(z:[E;10])->[E;10] {
 let mut absorption=z;
 for coordinate in [7usize,6] {absorption[coordinate]=E::ONE.sub(absorption[coordinate]);}
 absorption
}
fn owner_absorption(mut p:[E;10])->[E;10] {p[7]=E::ONE.sub(p[7]);p[6]=E::ONE.sub(p[6]);p}
#[cfg(kani)] mod point_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn successor_transition() {
  let p:[E;10]=unsafe {core::mem::transmute(kani::any::<[u32;10]>())};
  let out:[E;10]=unsafe {core::mem::transmute(kani::any::<[u32;10]>())};
  let left:u8=kani::any();kani::assume(left>0 && left<=10);
  let carry=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_successor_step(&p,out,(left-1) as usize,carry);let ta=trace();
  reset(answers);let b=owner_successor_step(p,out,left,carry);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,4);
 }
 #[kani::proof] #[kani::unwind(34)] fn absorption_complete() {
  let p:[E;10]=unsafe {core::mem::transmute(kani::any::<[u32;10]>())};let answers=kani::any();
  reset(answers);let a=native_absorption(p);let ta=trace();
  reset(answers);let b=owner_absorption(p);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
''')
p=E/'native/lib.rs';s=p.read_text()
if 'points-iterations.rs' not in s:s+='\ninclude!("points-iterations.rs");\n'
p.write_text(s)
p=Path('crates/aspis-core/src/state_only_prefix.rs');s=p.read_text();a=s.index('fn state_only_statement_points');b=s.index('\nfn encode_statement_points',a)
(E/'pins/points-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),literal=s[a:b],abstractions=['source successor at arbitrary legal reverse-iterator cursor, owned counter left=coordinate+1','complete two-cell absorption; all ten input/output cells retained','arithmetic answers universal and paired with exact operands/call order']),indent=2)+'\n')
