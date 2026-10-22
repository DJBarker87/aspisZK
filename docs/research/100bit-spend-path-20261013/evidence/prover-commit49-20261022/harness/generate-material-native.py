from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'material-binding.rs' not in s:s+='\ninclude!("material-binding.rs");\n'
p.write_text(s)
(E/'native/material-binding.rs').write_text('''
fn native_material_write(mut w:[E;1024],j:usize,cell:E)->[E;1024] {w[j]=cell;w}
fn owner_material_write(mut out:[E;1024],j:usize,cell:E)->[E;1024] {out[j]=cell;out}
#[cfg(kani)] mod material_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(1030)] fn outer_material_write() {
  let w:[E;1024]=unsafe{core::mem::transmute(kani::any::<[u32;1024]>())};
  let j:usize=kani::any();kani::assume(j<1024);let cell=E(kani::any());
  assert_eq!(native_material_write(w,j,cell),owner_material_write(w,j,cell));
 }
}
''')
p=Path('crates/aspis-r1-cost-probe/src/weights.rs')
(E/'pins/material-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),binding='The outer indexed materialization write, after the entire inner cell loop returns; arbitrary full initial array and legal index. The field arithmetic and inner loop are separate retained gates/Lean induction, not assumed true by this zero-call write check. Vec iteration/index and filled allocation remain standard-operation/caller boundaries.'),indent=2)+'\n')
