// Executable mirror of ResidualModel.lean versus the pinned source.
// Public prefixes remain unchanged; no privacy conclusion from these checks.
extern crate aspis_core as corelib;
use corelib::field::{M31,M31_HALF,M31_QUARTER,QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
mod fixed {include!("r17_basis_tables.rs");}
use r28_source_helpers::{chord,dot,times_x};
fn xentry(j:usize,r:usize)->K{let(mut row,mut bit)=(j,0);let mut sum=K::ZERO;while row&(1<<bit)!=0{row^=1<<bit;bit+=1;if row==r{sum=sum.add(K::ONE.mul_m31(M31_HALF).pow(bit as u64));}}if row|(1<<bit)==r{sum=sum.add(K::ONE.mul_m31(M31_HALF).pow(bit as u64));}sum}
fn xxentry(j:usize,r:usize)->K{(0..j+2).fold(K::ZERO,|s,i|s.add(xentry(j,i).mul(xentry(i,r))))}
fn delta(j:usize,r:usize)->K{if j==r{K::ONE}else{K::ZERO}}
fn centry(j:usize,r:usize,[a,b,c]:[K;3])->K{let d=delta(j/2,r/2);if j%2==0{if r%2==0{a.mul(d).add(b.mul(xentry(j/2,r/2)))}else{c.mul(d)}}else if r%2==0{c.mul(d.sub(xxentry(j/2,r/2)))}else{a.mul(d).add(b.mul(xentry(j/2,r/2)))}}
fn point(z:&[K;10],which:usize)->[K;10]{std::array::from_fn(|i|if which==0{z[i]}else if which==1{let carry=(i+1..10).fold(K::ONE,|s,j|s.mul(z[j]));z[i].add(carry).sub(z[i].mul(carry).add(z[i].mul(carry)))}else if i==6||i==7{K::ONE.sub(z[i])}else{z[i]})}
fn tensor(z:&[K;10],r:usize)->K{(0..10).fold(K::ONE,|s,i|s.mul(if (r>>(9-i))&1==0{K::ONE.sub(z[i])}else{z[i]}))}
fn shifted(p:&[K],n:usize)->[K;27]{let mut v=[K::ZERO;27];v[..23].copy_from_slice(p);for _ in 0..n{v=std::array::from_fn(|r|(0..27).fold(K::ZERO,|s,j|s.add(v[j].mul(xentry(j,r)))));}v}
fn quotient(p:&[K],col:usize,alpha:K)->[K;108]{let v=shifted(p,col/3);let slot=col%3+1;std::array::from_fn(|r|if r%4==0{alpha.pow(slot as u64).mul(v[r/4]).neg()}else if r%4==slot{v[r/4]}else{K::ZERO})}
fn poly(q:&[K;108],w:&[K;108],reverse:bool)->[K;7]{let mut out=[K::ZERO;7];for block in 0..27{for a in 0..4{for b in 0..4{let slot=if reverse{(4-b)%4}else{b};out[a+b]=out[a+b].add(q[4*block+a].mul(w[4*block+slot]).mul_m31(M31_QUARTER));}}}out}
