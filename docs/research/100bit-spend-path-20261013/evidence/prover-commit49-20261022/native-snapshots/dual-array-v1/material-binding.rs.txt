
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
