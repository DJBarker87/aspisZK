//! R12 actual-source G-factor tests. Research only.
#![cfg(feature = "insecure-spend-fixture")]
use aspis_core::{field::{CM31,M31,QM31},state_only_hiding::state_only_explicit_g_mask_factor};
use aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_active_row_masks_compiled_v1;
#[path="support/r12_data.rs"] mod data;
use data::*;
fn q(x:u32)->QM31{QM31::from_cm31(CM31::from_m31(M31(x)))}
fn bit(r:usize,k:usize)->bool{(r>>(9-k))&1!=0}
fn weight(k:usize)->u32{275+150*k as u32}
fn suffix_sum(r:usize,j:usize)->u32{(j..10).map(|k|weight(k)*u32::from(bit(r,k))).sum()}
fn row_response(row:usize,prefix:&[QM31],t:QM31)->QM31{
 let j=prefix.len();let mut z=[QM31::ZERO;10];let mut scale=QM31::ONE;
 for k in 0..j{z[k]=prefix[k];scale=scale.mul(if bit(row,k){prefix[k]}else{QM31::ONE.sub(prefix[k])});}
 z[j]=t;scale=scale.mul(if bit(row,j){t}else{QM31::ONE.sub(t)});
 for k in j+1..10{z[k]=q(u32::from(bit(row,k)));}
 state_only_explicit_g_mask_factor(&z).mul(scale)
}
fn response(pairs:&[[usize;2]],prefix:&[QM31],t:QM31)->QM31{pairs.iter().fold(QM31::ZERO,|s,p|s.add(row_response(p[0],prefix,t).sub(row_response(p[1],prefix,t))))}
fn interpolate(v:&[QM31])->Vec<QM31>{
 let n=v.len();let mut out=vec![QM31::ZERO;n];
 for i in 0..n{let mut b=vec![QM31::ONE];for j in 0..n{if i==j{continue}let x=q(j as u32);let inv=q(i as u32).sub(x).inv();let mut next=vec![QM31::ZERO;b.len()+1];for k in 0..b.len(){next[k]=next[k].sub(b[k].mul(x));next[k+1]=next[k+1].add(b[k]);}b=next.into_iter().map(|a|a.mul(inv)).collect();}for k in 0..n{out[k]=out[k].add(v[i].mul(b[k]));}}out
}
fn assert_full_rank(mut a:Vec<Vec<QM31>>){for k in 0..27{let p=(k..27).find(|&r|a[r][k]!=QM31::ZERO).expect("rank");a.swap(k,p);let inv=a[k][k].inv();for c in k..27{a[k][c]=a[k][c].mul(inv)}let pivot=a[k].clone();for r in k+1..27{let x=a[r][k];for c in k..27{a[r][c]=a[r][c].sub(x.mul(pivot[c]));}}}}
fn check_family(j:usize,pairs:Vec<Vec<[usize;2]>>,shifts:&[u32;27],prefix:&[QM31]){
 let active=pool_v1_pair_forest_copy_active_row_masks_compiled_v1();let mut matrix=vec![vec![QM31::ZERO;27];27];
 for(k,ps)in pairs.iter().enumerate(){for(pref,p)in ps.iter().enumerate(){for&r in p{assert_eq!(active[r>>4]&(1<<(r&15)),0);assert_eq!(r>>(10-j),pref);assert_eq!(suffix_sum(r,j),shifts[k]);}assert!(!bit(p[0],j)&&bit(p[1],j));}for earlier in 0..j{for t in 0..28{assert_eq!(response(ps,&prefix[..earlier],q(t)),QM31::ZERO);}}let vals:Vec<_>=(0..28).map(|t|response(ps,prefix,q(t))).collect();assert_eq!(vals[0].add(vals[1]),QM31::ZERO);let poly=interpolate(&vals);matrix[0][k]=poly[0];for s in 1..27{matrix[s][k]=poly[s+1];}}
 assert_full_rank(matrix)
}
#[test]fn r12_actual_g_factor_two_continuations_cover_zero_one_and_extension_prefixes(){
 let a=QM31{c0:CM31::new(M31(2),M31(3)),c1:CM31::new(M31(5),M31(7))};let b=QM31{c0:CM31::new(M31(11),M31(13)),c1:CM31::new(M31(17),M31(19))};
 for prefix in [[QM31::ZERO,QM31::ZERO],[QM31::ZERO,QM31::ONE],[QM31::ONE,QM31::ZERO],[QM31::ONE,QM31::ONE],[a,b]]{check_family(1,PAIRS_R1.iter().map(|p|p.to_vec()).collect(),&SHIFTS_R1,&prefix[..1]);check_family(2,PAIRS_R2.iter().map(|p|p.to_vec()).collect(),&SHIFTS_R2,&prefix);}
}
