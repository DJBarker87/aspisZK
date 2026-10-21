// Bounded vector step cuts. Scalar/backend results are inputs here; their
// computation is certified separately, so these roots isolate storage effects.
use super::*;
fn symbolic_prefix<const N:usize>(n:usize)->Vec<u32> {
 let values:[u32;N]=kani::any();let mut out=Vec::with_capacity(N);
 for i in 0..n {out.push(values[i]);} out
}
#[kani::proof] #[kani::unwind(112)]
fn constructor_gather_vec_step() {
 let count:usize=kani::any();kani::assume(count<22);
 let mut flat=symbolic_prefix::<110>(5*count);
 let mut zs=symbolic_prefix::<22>(count);
 let old_flat=flat.clone();let old_zs=zs.clone();let values:[u32;5]=kani::any();
 // Frozen extend_from_slice versus reference's five push statements.
 flat.extend_from_slice(&values);
 let mut reference=old_flat.clone();
 reference.push(values[0]);reference.push(values[1]);reference.push(values[2]);reference.push(values[3]);reference.push(values[4]);
 zs.push(values[4]);
 assert_eq!(flat.len(),5*(count+1));assert!(flat.len()<=110);
 assert_eq!(zs.len(),count+1);assert!(zs.len()<=22);
 let at:usize=kani::any();kani::assume(at<flat.len());assert_eq!(flat[at],reference[at]);
 let z:usize=kani::any();kani::assume(z<count+1);
 assert_eq!(zs[z],if z<count{old_zs[z]}else{values[4]});
}
#[kani::proof] #[kani::unwind(7)]
fn constructor_zero_check() {
 let values:[u32;5]=kani::any();
 assert_eq!(values.iter().any(|x|*x==0),values[0]==0 || values[1]==0 || values[2]==0 || values[3]==0 || values[4]==0);
}
#[kani::proof] #[kani::unwind(112)]
fn constructor_prefix_push_step() {
 let index:usize=kani::any();kani::assume(index<110);
 let mut prefixes=symbolic_prefix::<110>(index);let product:u32=kani::any();
 let before=prefixes.clone();prefixes.push(product);
 assert_eq!(prefixes.len(),index+1);assert!(prefixes.len()<=110);
 let at:usize=kani::any();kani::assume(at<=index);
 assert_eq!(prefixes[at],if at<index{before[at]}else{product});
}
#[kani::proof] #[kani::unwind(112)]
fn constructor_inverse_write_step() {
 let count:usize=kani::any();let index:usize=kani::any();
 kani::assume(count<=110 && 0<index && index<=count);
 let mut inverse=symbolic_prefix::<110>(count);let before=inverse.clone();
 let i=index-1;let product:u32=kani::any();inverse[i]=product;
 let observe:usize=kani::any();kani::assume(observe<count);
 assert_eq!(inverse.len(),count);
 assert_eq!(inverse[observe],if observe==i{product}else{before[observe]});
}
#[kani::proof] #[kani::unwind(112)]
fn constructor_group_push_step() {
 let count:usize=kani::any();let index:usize=kani::any();
 kani::assume(count<=22 && index<count);
 let flat=symbolic_prefix::<110>(5*count);
 let expected:[u32;5]=core::array::from_fn(|j|flat[5*index+j]);
 let mut groups:Vec<[u32;5]>=Vec::with_capacity(22);
 let entries:[[u32;5];22]=kani::any();for i in 0..index{groups.push(entries[i]);}
 groups.push([flat[5*index],flat[5*index+1],flat[5*index+2],flat[5*index+3],flat[5*index+4]]);
 assert_eq!(groups.len(),index+1);assert!(groups.len()<=22);
 let observe:usize=kani::any();let lane:usize=kani::any();kani::assume(observe<=index && lane<5);
 assert_eq!(groups[observe][lane],if observe==index{expected[lane]}else{entries[observe][lane]});
}
#[kani::proof] #[kani::unwind(112)]
fn constructor_zero_resize() {
 let n:usize=kani::any();kani::assume(n<=110);
 let mut flat_inverse=Vec::with_capacity(n);flat_inverse.resize(n,0u32);
 assert_eq!(flat_inverse.len(),n);
 let observe:usize=kani::any();kani::assume(observe<n);assert_eq!(flat_inverse[observe],0);
}
#[kani::proof] #[kani::unwind(68)]
fn batched_constructor_write_step() {
 let raw:[[u64;4];64]=kani::any();let index:usize=kani::any();kani::assume(index<64);
 let limbs:[u32;4]=kani::any();let mut v=raw.to_vec();
 v[index]=[limbs[0] as u64,limbs[1] as u64,limbs[2] as u64,limbs[3] as u64];
 let observe:usize=kani::any();let lane:usize=kani::any();kani::assume(observe<64 && lane<4);
 assert_eq!(v.len(),64);assert_eq!(v[observe][lane],if observe==index{limbs[lane] as u64}else{raw[observe][lane]});
}
