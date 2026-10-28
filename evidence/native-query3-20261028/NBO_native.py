from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
src=subprocess.check_output(['git','show',frozen+':crates/aspis-r1-cost-probe/src/candidate.rs'],text=True)
start=src.index('    let i = a.next;',src.index('fn query_values('));end=src.index('    let folded = line_fold_with_inverses',start)
prefix=src[start:end].replace('    let i = a.next;','    let i = next;')
prefix=prefix.replace('return Err(Error::Query);','return Err(Error::Query);')
code='''use super::*;
static mut NBO_EVENT:usize=0;
static mut NBO_COORD:usize=0;
static mut NBO_Q:usize=0;
static mut NBO_ALPHA:E=E::ZERO;
static mut NBO_DOTS:[E;4]=[E::ZERO;4];
static mut NBO_INV:[M31;5]=[M31::ZERO;5];
static mut NBO_FOLD:E=E::ZERO;
static mut NBO_VALUES:[E;4]=[E::ZERO;4];
static mut NBO_PROOF:*const u8=core::ptr::null();
static mut NBO_G:*const E=core::ptr::null();
static mut NBO_GEOM:*const QueryGeometry=core::ptr::null();
fn NBO_any_e()->E {let w:[u32;8]=kani::any();
 kani::assume(w[0]<2147483647);kani::assume(w[1]<2147483647);kani::assume(w[2]<2147483647);kani::assume(w[3]<2147483647);
 kani::assume(w[4]<2147483647);kani::assume(w[5]<2147483647);kani::assume(w[6]<2147483647);kani::assume(w[7]<2147483647);
 E::from_limbs(w).unwrap()}
fn NBO_open(proof:&[u8],i:usize)->&[u8] {unsafe {assert_eq!(NBO_EVENT,0);NBO_EVENT=1;assert_eq!(i,NBO_Q);assert_eq!(proof.as_ptr(),NBO_PROOF);}proof}
fn NBO_dots(q:&[u8],g:&[E;29])->[E;4] {unsafe {assert_eq!(NBO_EVENT,1);NBO_EVENT=2;assert_eq!(q.as_ptr(),NBO_PROOF);assert_eq!(g.as_ptr(),NBO_G);NBO_DOTS}}
fn NBO_inverse(geometry:&QueryGeometry,i:usize)->&[M31;5] {unsafe {assert_eq!(NBO_EVENT,2);NBO_EVENT=3;assert_eq!(geometry as *const _,NBO_GEOM);assert_eq!(i,NBO_Q);&NBO_INV}}
fn NBO_circle(alpha:E,dots:[E;4],inverse:&[M31;5])->E {unsafe {
 assert_eq!(NBO_EVENT,3);NBO_EVENT=4;let k=NBO_COORD;
 assert_eq!(alpha.to_limbs()[k],NBO_ALPHA.to_limbs()[k]);
 assert_eq!(dots[0].to_limbs()[k],NBO_DOTS[0].to_limbs()[k]);
 assert_eq!(dots[1].to_limbs()[k],NBO_DOTS[1].to_limbs()[k]);
 assert_eq!(dots[2].to_limbs()[k],NBO_DOTS[2].to_limbs()[k]);
 assert_eq!(dots[3].to_limbs()[k],NBO_DOTS[3].to_limbs()[k]);
 assert_eq!(inverse[k%5],NBO_INV[k%5]);NBO_FOLD}}
fn NBO_field(q:&[u8],s:usize)->E {unsafe {assert_eq!(NBO_EVENT,4+s);NBO_EVENT+=1;
 assert_eq!(q.len(),128);assert_eq!(q.as_ptr(),NBO_PROOF.add(672));NBO_VALUES[s]}}
// Literal frozen prefix. The only carrier factoring is a.next -> next.
fn NBO_prefix(proof:&[u8],p:&Prepared,next:usize,g:&[E;29],geometry:&QueryGeometry)->Result<(E,[E;4],[M31;5]),Error>{
'''+prefix+'''    Ok((folded,values,inverse))
}
fn NBO_prefix_case(){
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBO_any_e();let folded=NBO_any_e();let values=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBO_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 unsafe {NBO_Q=next;NBO_COORD=k;NBO_PROOF=proof.as_ptr();NBO_G=g.as_ptr();NBO_GEOM=&geometry;NBO_ALPHA=alpha;
 NBO_DOTS=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 NBO_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBO_FOLD=folded;NBO_VALUES=values;}
 let out=NBO_prefix(&proof,&p,next,&g,&geometry);
 if folded!=values[(u%4)as usize] {assert!(matches!(out,Err(Error::Query)));}
 else {let(f,v,inv)=out.unwrap();assert_eq!(f.to_limbs()[k],folded.to_limbs()[k]);
 let j:usize=kani::any();kani::assume(j<4);assert_eq!(v[j].to_limbs()[k],values[j].to_limbs()[k]);
 unsafe{assert_eq!(inv[k%5],NBO_INV[k%5]);}}
 unsafe{assert_eq!(NBO_EVENT,8);}
 kani::cover!(folded==values[(u%4)as usize]);kani::cover!(folded!=values[(u%4)as usize]);
}
#[kani::proof]
#[kani::unwind(1024)]
#[kani::stub(super::opening,NBO_open)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
fn NBO_prefix_all_g(){NBO_prefix_case()}
'''
(E/'NBO_native.rs.txt').write_text(code)
(E/'NBO_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision=frozen,source_sha256=hashlib.sha256(src.encode()).hexdigest(),prefix_frozen=src[start:end],prefix_factored=prefix,changes=['a.next supplied as next','success returns the exact reached folded/values/inverse cut'],credit='native prefix routing only; callee bridges remain separate; g pointee contents are unobserved by routing stub'),indent=2)+'\n')
