//! R11 source-bound active-G coefficient check (research only).
#![cfg(feature = "insecure-spend-fixture")]
use aspis_core::{field::{CM31, M31, QM31}, state_only_hiding::state_only_explicit_g_mask_factor};
use aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_active_row_masks_compiled_v1;
const ROWS: [usize;28] = [11,12,27,28,32,43,44,48,59,60,64,75,76,80,91,92,96,107,108,112,123,124,128,139,140,160,171,512];
fn q(n:u32)->QM31 { QM31::from_cm31(CM31::from_m31(M31(n))) }
fn point(t:QM31,b:usize)->[QM31;10] { let mut z=[QM31::ZERO;10]; z[0]=t; for j in 0..9 {z[j+1]=q(((b>>(8-j))&1)as u32)} z }
fn interpolate(v:&[QM31])->Vec<QM31>{
 let n=v.len(); let mut out=vec![QM31::ZERO;n];
 for i in 0..n { let mut b=vec![QM31::ONE];
  for j in 0..n { if i==j {continue}; let x=q(j as u32); let s=q(i as u32).sub(x).inv(); let mut next=vec![QM31::ZERO;b.len()+1];
   for k in 0..b.len() { next[k]=next[k].sub(b[k].mul(x)); next[k+1]=next[k+1].add(b[k]); }
   b=next.into_iter().map(|value|value.mul(s)).collect(); }
  for k in 0..n { out[k]=out[k].add(v[i].mul(b[k])); }
 } out
}
#[test]
fn r11_active_g_source_factor_has_full_degree_support() {
 let active=pool_v1_pair_forest_copy_active_row_masks_compiled_v1(); let mut matrix=Vec::new();
 for &r in &ROWS {assert_ne!(active[r>>4]&(1<<(r&15)),0);let values:Vec<_>=(0..28).map(|i|{let t=q(i);state_only_explicit_g_mask_factor(&point(t,r%512)).mul(if r<512{QM31::ONE.sub(t)}else{t})}).collect();matrix.push(interpolate(&values));}
 for pivot in 0..28 {let row=(pivot..28).find(|&r|matrix[r][pivot]!=QM31::ZERO).expect("active-G coefficient matrix singular");matrix.swap(pivot,row);let inv=matrix[pivot][pivot].inv();for c in pivot..28{matrix[pivot][c]=matrix[pivot][c].mul(inv)}for r in 0..28{if r!=pivot{let a=matrix[r][pivot];for c in pivot..28{matrix[r][c]=matrix[r][c].sub(a.mul(matrix[pivot][c]))}}}}
 for i in 0..28{for j in 0..28{assert_eq!(matrix[i][j],if i==j{QM31::ONE}else{QM31::ZERO})}}
}
