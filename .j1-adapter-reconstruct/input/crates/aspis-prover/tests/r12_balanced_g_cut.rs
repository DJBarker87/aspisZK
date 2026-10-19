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
fn inverse(mut a:Vec<Vec<QM31>>)->Vec<Vec<QM31>>{let n=a.len();let mut out=vec![vec![QM31::ZERO;n];n];for i in 0..n{out[i][i]=QM31::ONE;}for k in 0..n{let p=(k..n).find(|&r|a[r][k]!=QM31::ZERO).expect("fixed inverse");a.swap(k,p);out.swap(k,p);let inv=a[k][k].inv();for c in 0..n{a[k][c]=a[k][c].mul(inv);out[k][c]=out[k][c].mul(inv);}let ar=a[k].clone();let or=out[k].clone();for r in 0..n{if r!=k{let x=a[r][k];for c in 0..n{a[r][c]=a[r][c].sub(x.mul(ar[c]));out[r][c]=out[r][c].sub(x.mul(or[c]));}}}}out}
fn mv(a:&[Vec<QM31>],v:&[QM31])->Vec<QM31>{a.iter().map(|row|row.iter().zip(v).fold(QM31::ZERO,|s,(x,y)|s.add(x.mul(*y)))).collect()}
fn eval(c:&[QM31],x:QM31)->QM31{c.iter().rev().fold(QM31::ZERO,|s,a|s.mul(x).add(*a))}
fn compact(c:&[QM31])->Vec<QM31>{core::iter::once(c[0]).chain(c[2..28].iter().copied()).collect()}
fn translate(c:&[QM31],shift:QM31)->Vec<QM31>{let values:Vec<_>=(0..c.len()).map(|x|eval(c,q(x as u32).add(shift))).collect();interpolate(&values)}
fn fixed_inverses(j:usize,shifts:&[u32;27])->(Vec<Vec<QM31>>,Vec<Vec<QM31>>){
 let mut t=vec![vec![QM31::ZERO;27];27];for col in 0..27{let values:Vec<_>=(0..28).map(|x|{let x=q(x);QM31::ONE.sub(x).mul(x.pow(col as u64)).sub(x.mul(x.sub(QM31::ONE).pow(col as u64))) }).collect();let c=compact(&interpolate(&values));for row in 0..27{t[row][col]=c[row];}}
 let c=q(weight(j));let mut moment=vec![vec![QM31::ZERO;27];27];for(col,&a)in shifts.iter().enumerate(){let values:Vec<_>=(0..27).map(|x|QM31::ONE.add(c.mul(q(x)).add(q(a)).pow(26))).collect();let p=interpolate(&values);for row in 0..27{moment[row][col]=p[row];}}
 (inverse(t),inverse(moment))
}
fn lift_target(j:usize,prefix:&[QM31],pairs:&[Vec<[usize;2]>],t_inv:&[Vec<QM31>],m_inv:&[Vec<QM31>],sent:&[QM31])->Vec<QM31>{let h=mv(t_inv,sent);let d=prefix.iter().enumerate().fold(QM31::ZERO,|s,(k,a)|s.add(q(weight(k)).mul(*a)));let h0=translate(&h,d.mul(q(weight(j)).inv()).neg());let coeff=mv(m_inv,&h0);let mut delta=vec![QM31::ZERO;1024];for(u,ps)in coeff.into_iter().zip(pairs){for [r,s] in ps{delta[*r]=delta[*r].add(u);delta[*s]=delta[*s].sub(u);}}delta}
fn check_family(j:usize,pairs:Vec<Vec<[usize;2]>>,shifts:&[u32;27],prefix:&[QM31]){
 let active=pool_v1_pair_forest_copy_active_row_masks_compiled_v1();let mut matrix=vec![vec![QM31::ZERO;27];27];
 for(k,ps)in pairs.iter().enumerate(){for(pref,p)in ps.iter().enumerate(){for&r in p{assert_eq!(active[r>>4]&(1<<(r&15)),0);assert_eq!(r>>(10-j),pref);assert_eq!(suffix_sum(r,j),shifts[k]);}assert!(!bit(p[0],j)&&bit(p[1],j));}for earlier in 0..j{for t in 0..28{assert_eq!(response(ps,&prefix[..earlier],q(t)),QM31::ZERO);}}let vals:Vec<_>=(0..28).map(|t|response(ps,prefix,q(t))).collect();assert_eq!(vals[0].add(vals[1]),QM31::ZERO);let poly=interpolate(&vals);matrix[0][k]=poly[0];for s in 1..27{matrix[s][k]=poly[s+1];}}
 assert_full_rank(matrix)
}
#[test]fn r12_actual_g_factor_two_continuations_cover_zero_one_and_extension_prefixes(){
 let a=QM31{c0:CM31::new(M31(2),M31(3)),c1:CM31::new(M31(5),M31(7))};let b=QM31{c0:CM31::new(M31(11),M31(13)),c1:CM31::new(M31(17),M31(19))};
 for prefix in [[QM31::ZERO,QM31::ZERO],[QM31::ZERO,QM31::ONE],[QM31::ONE,QM31::ZERO],[QM31::ONE,QM31::ONE],[a,b]]{check_family(1,PAIRS_R1.iter().map(|p|p.to_vec()).collect(),&SHIFTS_R1,&prefix[..1]);check_family(2,PAIRS_R2.iter().map(|p|p.to_vec()).collect(),&SHIFTS_R2,&prefix);}
}

#[test]fn r12_fixed_inverse_translation_lifts_every_compact_coordinate(){
 let ext=QM31{c0:CM31::new(M31(2),M31(3)),c1:CM31::new(M31(5),M31(7))};let prefixes=[[QM31::ZERO,QM31::ZERO],[QM31::ONE,QM31::ONE],[ext,ext.mul(ext)]];
 for(j,pairs,shifts)in[(1,PAIRS_R1.iter().map(|p|p.to_vec()).collect::<Vec<_>>(),&SHIFTS_R1),(2,PAIRS_R2.iter().map(|p|p.to_vec()).collect::<Vec<_>>(),&SHIFTS_R2)]{let(t_inv,m_inv)=fixed_inverses(j,shifts);for prefix in &prefixes{for target_index in 0..28{let sent:Vec<_>=if target_index<27{(0..27).map(|k|if k==target_index{ext}else{QM31::ZERO}).collect()}else{(0..27).map(|k|ext.mul(q(k as u32+1))).collect()};let delta=lift_target(j,&prefix[..j],&pairs,&t_inv,&m_inv,&sent);assert_eq!(delta.iter().copied().fold(QM31::ZERO,QM31::add),QM31::ZERO);for earlier in 0..j{for x in 0..28{let total=(0..1024).filter(|&r|delta[r]!=QM31::ZERO).fold(QM31::ZERO,|s,r|s.add(delta[r].mul(row_response(r,&prefix[..earlier],q(x)))));assert_eq!(total,QM31::ZERO);}}let values:Vec<_>=(0..28).map(|x|(0..1024).filter(|&r|delta[r]!=QM31::ZERO).fold(QM31::ZERO,|s,r|s.add(delta[r].mul(row_response(r,&prefix[..j],q(x)))))).collect();assert_eq!(compact(&interpolate(&values)),sent);}}}
}
