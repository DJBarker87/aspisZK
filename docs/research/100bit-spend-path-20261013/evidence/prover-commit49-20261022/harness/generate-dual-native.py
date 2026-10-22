from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'dual-binding.rs' not in s:s+='\ninclude!("dual-binding.rs");\n'
p.write_text(s)
(E/'native/dual-binding.rs').write_text('''
fn dual_horner49(h:[E;4],a:E)->E {
 h[0].add(a.mul(h[3].add(a.mul(h[2].add(a.mul(h[1])))))).mul_m31(M31(536870912))
}
fn native_dual_array49(q:[E;1024],a:E,mut out:[E;256],i:usize)->[E;256] {
 let h=[q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]];out[i]=dual_horner49(h,a);out
}
fn owner_dual_array49(q:[E;1024],a:E,mut out:[E;256],i:usize)->[E;256] {
 let h=[q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]];out[i]=dual_horner49(h,a);out
}
#[cfg(kani)] mod dual_array_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(1300)] fn full_dual_array_iteration() {
  let q:[E;1024]=unsafe{core::mem::transmute(kani::any::<[u32;1024]>())};
  let out:[E;256]=unsafe{core::mem::transmute(kani::any::<[u32;256]>())};
  let i:usize=kani::any();kani::assume(i<256);let a=E(kani::any());let answers=kani::any();
  reset(answers);let x=native_dual_array49(q,a,out,i);let tx=trace();
  reset(answers);let y=owner_dual_array49(q,a,out,i);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,7);
 }
}
''')
p=Path('crates/aspis-r1-cost-probe/src/prover.rs')
(E/'pins/dual-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),binding='Full 1024-input/256-output dual-fold iteration: all four selected source inputs, whole output context, legal index, complete callee operand/order trace. Actual cell arithmetic is the identical retained dual_cell declaration from part48.'),indent=2)+'\n')
