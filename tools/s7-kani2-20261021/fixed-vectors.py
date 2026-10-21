#!/usr/bin/env python3
from pathlib import Path
import sys
T=Path(__file__).resolve().parent
s='use super::*;\n'
s+='''fn gather<const C:usize>() {
 let values:[u32;5]=kani::any();let old:[u32;110]=kani::any();let zold:[u32;22]=kani::any();
 let mut flat=old[..5*C].to_vec();let mut zs=zold[..C].to_vec();
 // Capacity is explicitly available before the step.
 flat.reserve_exact(5);zs.reserve_exact(1);
 let mut reference=flat.clone();reference.reserve_exact(5);
 flat.extend_from_slice(&values);
 reference.push(values[0]);reference.push(values[1]);reference.push(values[2]);reference.push(values[3]);reference.push(values[4]);
 zs.push(values[4]);
 assert_eq!(flat.len(),5*(C+1));assert!(flat.len()<=110);
 assert_eq!(zs.len(),C+1);assert!(zs.len()<=22);
 let at:usize=kani::any();kani::assume(at<5*(C+1));assert_eq!(flat[at],reference[at]);
 let i:usize=kani::any();kani::assume(i<=C);assert_eq!(zs[i],if i<C{zold[i]}else{values[4]});
}
fn prefix<const I:usize>() {
 let old:[u32;110]=kani::any();let product:u32=kani::any();let mut out=old[..I].to_vec();out.reserve_exact(1);out.push(product);
 assert_eq!(out.len(),I+1);assert!(out.len()<=110);
 let observe:usize=kani::any();kani::assume(observe<=I);assert_eq!(out[observe],if observe<I{old[observe]}else{product});
}
fn inverse<const I:usize>() {
 let old:[u32;110]=kani::any();let value:u32=kani::any();let mut out=old.to_vec();out[I]=value;
 let observe:usize=kani::any();kani::assume(observe<110);
 assert_eq!(out.len(),110);assert_eq!(out[observe],if observe==I{value}else{old[observe]});
}
fn grouping<const I:usize>() {
 let old:[[u32;5];22]=kani::any();let flat:[u32;110]=kani::any();let mut out=old[..I].to_vec();out.reserve_exact(1);
 let expected:[u32;5]=core::array::from_fn(|j|flat[5*I+j]);
 out.push([flat[5*I],flat[5*I+1],flat[5*I+2],flat[5*I+3],flat[5*I+4]]);
 assert_eq!(out.len(),I+1);assert!(out.len()<=22);
 let observe:usize=kani::any();let lane:usize=kani::any();kani::assume(observe<=I && lane<5);
 assert_eq!(out[observe][lane],if observe==I{expected[lane]}else{old[observe][lane]});
}
fn resize<const N:usize>() {
 let mut out=Vec::with_capacity(N);out.resize(N,0u32);assert_eq!(out.len(),N);
 let observe:usize=kani::any();kani::assume(observe<N);assert_eq!(out[observe],0);
}
'''
for root,count,callee in [('gather',22,'gather'),('prefix',110,'prefix'),('inverse',110,'inverse'),('group',22,'grouping'),('resize',111,'resize')]:
 for i in range(count):s+=f'#[kani::proof] #[kani::unwind(112)] fn fixed_{root}_{i}() {{{callee}::<{i}>();}}\n'
if '--check' in sys.argv:assert (T/'src/vectors_fixed.rs').read_text()==s
else:(T/'src/vectors_fixed.rs').write_text(s)
