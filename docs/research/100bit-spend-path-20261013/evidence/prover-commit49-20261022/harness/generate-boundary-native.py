from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
s=Path('crates/aspis-core/src/state_only_sumcheck.rs').read_text();a=s.index('    let first = polynomial[0];',s.index('pub fn state_only_boundary_sum'));b=s.index('    QM31 {',a)
body=s[a:b]
(E/'native/boundary-iterations.rs').write_text('''
#[derive(Clone,Copy)] struct M(u32);
#[derive(Clone,Copy)] struct C { a:M,b:M }
#[derive(Clone,Copy)] struct K { c0:C,c1:C }
fn native_boundary_sums(polynomial:&[K;28])->[u64;4] {
'''+body+'''    limbs
}
fn owner_boundary_limb(q:[u32;28])->u64 {
 let mut total=2*u64::from(q[0]);
 for i in 1..28 {total+=u64::from(q[i]);}
 total
}
#[cfg(kani)] mod boundary_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(30)] fn complete_limb_accumulation() {
  let raw:[[u32;4];28]=kani::any();
  let q=raw.map(|x|K{c0:C{a:M(x[0]),b:M(x[1])},c1:C{a:M(x[2]),b:M(x[3])}});
  let actual=native_boundary_sums(&q);
  for lane in 0..4 {
   let words=raw.map(|x|x[lane]);
   assert_eq!(actual[lane],owner_boundary_limb(words));
  }
 }
}
''')
p=E/'native/lib.rs';s=p.read_text()
if 'boundary-iterations.rs' not in s:s+='\ninclude!("boundary-iterations.rs");\n'
p.write_text(s)
p=Path('crates/aspis-core/src/state_only_sumcheck.rs')
(E/'pins/boundary-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),literal_accumulator=body,abstractions=['QM31/CM31/M31 have literal named scalar fields; no field calls are stubbed','returns the four integer accumulators before reduction; source reducer proof is separate','reference splits full 28-entry array into four limb arrays']),indent=2)+'\n')
