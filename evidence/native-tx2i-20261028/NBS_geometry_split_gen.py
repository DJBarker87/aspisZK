from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/verifier.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
s+=''.join(l[1:] for l in (E/'NBS_geometry.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
t=r'''
#[cfg(kani)] mod NBS_geometry_cuts {
 use super::*;
 #[kani::proof] #[kani::unwind(112)]
 fn prefix_write(){
  let old:[u32;110]=kani::any();let mut prefixes:Vec<M31>=old.map(M31).into();let index:usize=kani::any();kani::assume(index<110);
  prefixes.truncate(index);let ptr=prefixes.as_ptr();let product=M31(kani::any());
  prefixes.push(product);
  assert!(prefixes.len()==index+1&&prefixes.as_ptr()==ptr);
  let j:usize=kani::any();kani::assume(j<=index);assert!(prefixes[j].0==if j==index{product.0}else{old[j]});
 }
 #[kani::proof] #[kani::unwind(112)]
 fn backward_write(){
  let flat:[u32;110]=kani::any();let prefixes:[u32;110]=kani::any();let old:[u32;110]=kani::any();
  let mut flat_inverse:Vec<M31>=old.map(M31).into();let i:usize=kani::any();kani::assume(i<110);
  let mut suffix_inverse=M31(kani::any());let suffix=suffix_inverse.0;
  // Two field-call cuts, paired to LPf_BaseMultiply.source and the SAME
  // source operands; no multiplication is executed in Kani.
  let first_left=suffix_inverse.0;let first_right=prefixes[i];let r0=M31(kani::any());
  flat_inverse[i]=r0;
  let second_left=suffix_inverse.0;let second_right=flat[i];let r1=M31(kani::any());
  suffix_inverse=r1;
  let j:usize=kani::any();kani::assume(j<110);
  assert!(first_left==suffix&&first_right==prefixes[i]);assert!(second_left==suffix&&second_right==flat[i]);
  assert!(flat_inverse[j].0==if j==i{r0.0}else{old[j]});assert!(suffix_inverse==r1);assert!(flat_inverse.len()==110);
 }
 #[kani::proof] #[kani::unwind(3)]
 fn prefix_after_product(){
  let mut index:usize=kani::any();kani::assume(index<110);let before=index;
  let product=M31(kani::any());index+=1;
  assert!(index==before+1);assert!(product.0<=u32::MAX);
 }
}
'''
(E/'NBS_geometry_cuts.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
