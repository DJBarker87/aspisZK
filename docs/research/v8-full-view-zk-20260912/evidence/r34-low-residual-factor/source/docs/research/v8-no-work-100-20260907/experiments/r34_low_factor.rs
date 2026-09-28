//! Low residual: source-functional simplification and query-factor basis change.
//! Only the two retained prefixes are transcripts; coefficient probes are algebra.
extern crate aspis_core as corelib;
use corelib::field::{M31, M31_HALF, QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g; mod r17_mask_workspace; mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
use r28_source_helpers::{chord,dot,times_x};
const ROWS:[usize;13]=[1,2,3,4,5,6,7,8,10,11,12,13,15];
fn channel(v:&[K],slot:usize,a:K)->Vec<K>{let mut q=vec![K::ZERO;1024];for(i,&x)in v.iter().enumerate(){q[4*i+slot]=x;q[4*i]=a.pow(slot as u64).mul(x).neg();}q}
fn det(mut a:Vec<Vec<K>>)->K{let mut d=K::ONE;for j in 0..a.len(){let Some(p)=(j..a.len()).find(|&i|a[i][j]!=K::ZERO)else{return K::ZERO};if p!=j{a.swap(p,j);d=d.neg();}let v=a[j][j];d=d.mul(v);let inv=v.inv();for i in j+1..a.len(){let s=a[i][j].mul(inv);for h in j+1..a.len(){a[i][h]=a[i][h].sub(s.mul(a[j][h]));}}}d}
fn observations(q:&[K],abc:[K;3],point:&[Vec<K>],rw:&WeightAccumulator,gw:&WeightAccumulator)->Vec<K>{
    let m=basis_transport::transport().inverse(&chord(q,abc));
    let coins=structured_g::mixed_coins(&m);assert!(coins.iter().all(|&x|x==K::ZERO));
    let mut out=vec![K::ZERO,dot(&point[1],&m),dot(&point[2],&m)];
    out.extend(polynomial_for_extension(q,rw));out.extend(polynomial_for_extension(q,gw));out
}
fn factors(p:&[K],alpha:K)->Vec<Vec<K>>{let mut v=p.to_vec();let mut out=Vec::new();for j in 0..5{for s in 1..4{if j<4||s==1{out.push(channel(&v,s,alpha));}}v=times_x(&v);}out}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),4);
    let b=std::fs::read(&args[1]).unwrap();assert_eq!(b.len(),424);
    let f:Vec<_>=b[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();
    let z:[K;10]=f[..10].try_into().unwrap();let(k,tau,alpha)=(f[10],f[11],f[12]);
    let(sx,sy,zx,zy)=(f[13],f[14],f[15],f[16]);let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=b[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();
    let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let mut p=vec![K::ONE];for pt in &points{let r=pt.x.mul(pt.x).double().sub(M31::ONE);let mut n=times_x(&p);for j in 0..p.len(){n[j]=n[j].sub(p[j].mul_m31(r));}p=n;}assert_eq!(p.len(),23);
    let map=basis_transport::transport();
    let point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(&z).iter().map(|z|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
    let rw=opening_weights::quotient_weights(&z,k,abc,tau,false);let gw=opening_weights::quotient_weights(&z,k,abc,tau,true);
    let pw:Vec<Vec<K>>=point.iter().map(|p|opening_weights::chord_transpose(&map.dual(p),abc)).collect();
    // Entire 4-slot chunks, not merely scalar pairings with q. This retains all
    // seven first-polynomial coefficients, including off-diagonal products.
    for i in 0..108{let tail=k.pow(2).mul(pw[1][i]).add(k.pow(3).mul(pw[2][i]));assert_eq!(rw.weight_at(i as u32),k.mul(pw[0][i]).add(tail));assert_eq!(gw.weight_at(i as u32),tail);}
    let qcols=factors(&p,alpha);assert_eq!(qcols.len(),13);
    let obs:Vec<_>=qcols.iter().map(|q|observations(q,abc,&point,&rw,&gw)).collect();
    let mut normalized=Vec::new();let mut multiples=Vec::new();let mut v=p.clone();for _ in 0..5{multiples.push(v.clone());v=times_x(&v);}
    for d in 22..27{let mut rem=vec![K::ZERO;27];rem[d]=K::ONE;for h in(22..=d).rev(){let s=rem[h].mul(multiples[h-22][h].inv());for j in 0..=h{rem[j]=rem[j].sub(s.mul(multiples[h-22][j]));}}assert!(rem[22..].iter().all(|&x|x==K::ZERO));let mut v:Vec<_>=rem.iter().map(|x|x.neg()).collect();v[d]=K::ONE;for s in 1..4{if d<26||s==1{normalized.push(channel(&v,s,alpha));}}}
    let normal:Vec<_>=normalized.iter().map(|q|observations(q,abc,&point,&rw,&gw)).collect();
    let old=std::fs::read(&args[2]).unwrap();let encoded:Vec<_>=old.chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();assert_eq!(encoded.len(),169);
    for(i,&r)in ROWS.iter().enumerate(){for j in 0..13{assert_eq!(normal[j][r],encoded[13*i+j]);}}
    let mut change=vec![vec![K::ZERO;13];13];for j in 0..13{let s=j%3+1;let mult=&multiples[j/3];for i in 0..13{if i%3+1==s&&22+i/3<mult.len(){change[i][j]=mult[22+i/3];}if i>j{assert_eq!(change[i][j],K::ZERO);}}}
    for j in 0..13{for h in 0..1024{assert_eq!(qcols[j][h],(0..13).fold(K::ZERO,|s,i|s.add(normalized[i][h].mul(change[i][j]))));}for r in 0..17{assert_eq!(obs[j][r],(0..13).fold(K::ZERO,|s,i|s.add(normal[i][r].mul(change[i][j]))));}}
    let half=K::ONE.mul_m31(M31_HALF);for j in 0..13{let d=22+j/3;assert_eq!(change[j][j],half.pow((d-d.count_ones()as usize)as u64));}
    assert_eq!(det(change.clone()),half.pow(269));
    let nm:Vec<Vec<K>>=ROWS.iter().map(|&r|normal.iter().map(|v|v[r]).collect()).collect();let fm:Vec<Vec<K>>=ROWS.iter().map(|&r|obs.iter().map(|v|v[r]).collect()).collect();
    let dn=det(nm);let df=det(fm);assert_ne!(dn,K::ZERO);assert_eq!(df,dn.mul(half.pow(269)));
    // Algebra probes: coefficients of arbitrary degree <=22 P, NOT new sampled
    // prefixes. The full residual matrix is linear in the 23 coefficients.
    let mut accum=vec![vec![K::ZERO;17];13];
    for d in 0..23{let mut e=vec![K::ZERO;23];e[d]=K::ONE;for(j,q)in factors(&e,alpha).iter().enumerate(){let o=observations(q,abc,&point,&rw,&gw);for r in 0..17{accum[j][r]=accum[j][r].add(p[d].mul(o[r]));}}}assert_eq!(accum,obs);
    // Wrong normalization and omission of first-point subtraction must be seen.
    assert_ne!(df,dn);assert!((0..108).any(|i|rw.weight_at(i)!=gw.weight_at(i)));
    let out=std::path::Path::new(&args[3]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    std::fs::write(out.join("summary.json"),"{\"source_prefixes\":1,\"source_low_weight_equalities\":216,\"source_minor_entries\":169,\"basis_vector_equalities\":13312,\"residual_basis_equalities\":221,\"coefficient_probes\":299,\"coefficient_reconstruction_equalities\":221,\"determinant_scale_half_exponent\":269,\"negative_controls\":2,\"universal_coverage\":false,\"full_privacy\":false}\n").unwrap();
    println!("R34_LOW_FACTOR source_weights=216 old_minor=169 vector_equalities=13312 residual_equalities=221 algebra_probes=299 det_scale=half^269 full_privacy=false");
}
