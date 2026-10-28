extern crate alloc;
include!("KMX_stubs.rs");
use super::*;
static mut NBZ_EVENT:usize=0;
static mut NBZ_COORD:usize=0;
static mut NBZ_Q:usize=0;
static mut NBZ_ALPHA:E=E::ZERO;
static mut NBZ_DOTS:[E;4]=[E::ZERO;4];
static mut NBZ_INV:[M31;5]=[M31::ZERO;5];
static mut NBZ_FOLD:E=E::ZERO;
static mut NBZ_VALUES:[E;4]=[E::ZERO;4];
static mut NBZ_PROOF:*const u8=core::ptr::null();
static mut NBZ_G:*const E=core::ptr::null();
static mut NBZ_GEOM:*const QueryGeometry=core::ptr::null();
fn NBZ_any_e()->E {let w:[u32;8]=kani::any();
 kani::assume(w[0]<2147483647);kani::assume(w[1]<2147483647);kani::assume(w[2]<2147483647);kani::assume(w[3]<2147483647);
 kani::assume(w[4]<2147483647);kani::assume(w[5]<2147483647);kani::assume(w[6]<2147483647);kani::assume(w[7]<2147483647);
 E::from_limbs(w).unwrap()}
fn NBZ_open(proof:&[u8],i:usize)->&[u8] {unsafe {assert_eq!(NBZ_EVENT,0);NBZ_EVENT=1;assert_eq!(i,NBZ_Q);assert_eq!(proof.as_ptr(),NBZ_PROOF);}proof}
fn NBZ_dots(q:&[u8],g:&[E;29])->[E;4] {unsafe {assert_eq!(NBZ_EVENT,1);NBZ_EVENT=2;assert_eq!(q.as_ptr(),NBZ_PROOF);assert_eq!(g.as_ptr(),NBZ_G);NBZ_DOTS}}
fn NBZ_inverse(geometry:&QueryGeometry,i:usize)->&[M31;5] {unsafe {assert_eq!(NBZ_EVENT,2);NBZ_EVENT=3;assert_eq!(geometry as *const _,NBZ_GEOM);assert_eq!(i,NBZ_Q);&NBZ_INV}}
fn NBZ_circle(alpha:E,dots:[E;4],inverse:&[M31;5])->E {unsafe {
 assert_eq!(NBZ_EVENT,3);NBZ_EVENT=4;let k=NBZ_COORD;
 assert_eq!(alpha.to_limbs()[k],NBZ_ALPHA.to_limbs()[k]);
 assert_eq!(dots[0].to_limbs()[k],NBZ_DOTS[0].to_limbs()[k]);
 assert_eq!(dots[1].to_limbs()[k],NBZ_DOTS[1].to_limbs()[k]);
 assert_eq!(dots[2].to_limbs()[k],NBZ_DOTS[2].to_limbs()[k]);
 assert_eq!(dots[3].to_limbs()[k],NBZ_DOTS[3].to_limbs()[k]);
 assert_eq!(inverse[k%5],NBZ_INV[k%5]);NBZ_FOLD}}
fn NBZ_field(q:&[u8],s:usize)->E {unsafe {assert_eq!(NBZ_EVENT,4+s);NBZ_EVENT+=1;
 assert_eq!(q.len(),128);assert_eq!(q.as_ptr(),NBZ_PROOF.add(672));NBZ_VALUES[s]}}
// Literal frozen prefix. The only carrier factoring is a.next -> next.
fn NBZ_prefix(proof:&[u8],p:&Prepared,next:usize,g:&[E;29],geometry:&QueryGeometry)->Result<(E,[E;4],[M31;5]),Error>{
    let i = next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    crate::trace::value(9, 4 * i, dots[0]);
    crate::trace::value(9, 4 * i + 1, dots[1]);
    crate::trace::value(9, 4 * i + 2, dots[2]);
    crate::trace::value(9, 4 * i + 3, dots[3]);
    let inverse = *geometry.for_query(i);
    let folded = circle_fold_with_inverses(p.alpha[0], dots, &inverse);
    crate::trace::value(10, 2 * i, folded);
    let values = core::array::from_fn(|s| field(&q[672..800], s));
    if folded != values[u % 4] {
        return Err(Error::Query);
    }
    Ok((folded,values,inverse))
}
fn NBZ_prefix_case(){
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 let out=NBZ_prefix(&proof,&p,next,&g,&geometry);
 if folded!=values[(u%4)as usize] {assert!(matches!(out,Err(Error::Query)));}
 else {let(f,v,inv)=out.unwrap();assert_eq!(f.to_limbs()[k],folded.to_limbs()[k]);
 let j:usize=kani::any();kani::assume(j<4);assert_eq!(v[j].to_limbs()[k],values[j].to_limbs()[k]);
 unsafe{assert_eq!(inv[k%5],NBZ_INV[k%5]);}}
 unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(folded==values[(u%4)as usize]);kani::cover!(folded!=values[(u%4)as usize]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
#[kani::stub(super::opening,NBZ_open)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
fn NBZ_prefix_all_g(){NBZ_prefix_case()}

// Capacity is arbitrary throughout the native allocation layout domain.
// This checks one indexed slice setter, never the query or row loop.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_capacity_row() {
 let cap:usize=kani::any();kani::assume(cap>=64);kani::assume(cap<=isize::MAX as usize/core::mem::size_of::<[u64;4]>());
 let initial:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];
 let mut raw:Vec<[u64;4]>=Vec::with_capacity(cap);raw.extend_from_slice(&initial);
 assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);let ptr=raw.as_ptr();
 let i:usize=kani::any();kani::assume(i<64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let new:[u64;4]=kani::any();let before=raw[j][k];
 raw[i]=new;
 assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);assert_eq!(raw.as_ptr(),ptr);
 assert_eq!(raw[j][k],if i==j {new[k]}else{before});
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(i!=j);
}

static mut NBZ_ALPHA1:E=E::ZERO;
static mut NBZ_LINE:E=E::ZERO;
static mut NBZ_LINE_CALLS:usize=0;
fn NBZ_line(alpha:E,values:[E;4],inverse:&[M31;5])->E {unsafe {
 NBZ_LINE_CALLS+=1;let k=NBZ_COORD;assert_eq!(alpha.to_limbs()[k],NBZ_ALPHA1.to_limbs()[k]);
 assert_eq!(values[0].to_limbs()[k],NBZ_VALUES[0].to_limbs()[k]);
 assert_eq!(values[1].to_limbs()[k],NBZ_VALUES[1].to_limbs()[k]);
 assert_eq!(values[2].to_limbs()[k],NBZ_VALUES[2].to_limbs()[k]);
 assert_eq!(values[3].to_limbs()[k],NBZ_VALUES[3].to_limbs()[k]);
 assert_eq!(inverse[k%5],NBZ_INV[k%5]);NBZ_LINE}}
// Literal source continuation up to the node field-operation cut.
fn NBZ_line_geometry(alpha:E,values:[E;4],inverse:&[M31;5],i:usize,geometry:&QueryGeometry)->(E,M31) {
 let folded=line_fold_with_inverses(alpha,values,inverse);
 crate::trace::value(10,2*i+1,folded);
 let z=geometry.line_z[i-geometry.start];
 (folded,z)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_line)]
fn NBZ_line_geometry_routing() {
 let i:usize=kani::any();kani::assume(i<10);let start:usize=kani::any();kani::assume(start<=i);
 let k:usize=kani::any();kani::assume(k<8);let alpha=NBZ_any_e();let line=NBZ_any_e();
 let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let inverse=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let zs:[u32;10]=kani::any();
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from([
 M31(zs[0]),M31(zs[1]),M31(zs[2]),M31(zs[3]),M31(zs[4]),M31(zs[5]),M31(zs[6]),M31(zs[7]),M31(zs[8]),M31(zs[9])])};
 unsafe{NBZ_COORD=k;NBZ_ALPHA1=alpha;NBZ_LINE=line;NBZ_VALUES=values;NBZ_INV=inverse;}
 let(out,z)=NBZ_line_geometry(alpha,values,&inverse,i,&geometry);
 assert_eq!(out.to_limbs()[k],line.to_limbs()[k]);assert_eq!(z.0,zs[i-start]);
 assert_eq!(geometry.start,start);assert_eq!(geometry.line_z.len(),10);
 unsafe{assert_eq!(NBZ_LINE_CALLS,1);}
 kani::cover!(start==i);kani::cover!(i==9);kani::cover!(start<i);
}
// Counter/assignment cut after rhs and power have returned. All returned
// carriers are unconstrained here; their operations and domains remain explicit.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
fn NBZ_tail_assignment() {
 let mut next:usize=kani::any();kani::assume(next<10);let mut terms:usize=kani::any();kani::assume(terms==next);
 let old=next;let mut rhs=NBZ_any_e();let old_rhs=rhs;let returned_rhs=NBZ_any_e();
 let mut power=K::ZERO;let returned_power=NBZ_any_e().c0();let k:usize=kani::any();kani::assume(k<8);
 terms+=1;
 assert_eq!(rhs.to_limbs()[k],old_rhs.to_limbs()[k]);
 rhs=returned_rhs;crate::trace::value(11,next,rhs);
 power=returned_power;next+=1;
 assert_eq!(next,old+1);assert_eq!(terms,next);assert_eq!(rhs.to_limbs()[k],returned_rhs.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(power)[k%4],words(returned_power)[k%4]);
 kani::cover!(old==0);kani::cover!(old==9);
}

fn NBZ_project_capacity<T:Copy,const N:usize>(initial:[T;N],cap:usize) {
 kani::assume(cap>=N);kani::assume(cap<=isize::MAX as usize/core::mem::size_of::<T>());
 let mut v:Vec<T>=Vec::with_capacity(cap);v.extend_from_slice(&initial);
 let ptr=v.as_ptr();assert_eq!(v.len(),N);assert_eq!(v.capacity(),cap);
 {let s:&[T]=&v;assert_eq!(s.len(),N);assert_eq!(s.as_ptr(),ptr);}
 {let s:&mut[T]=&mut v;assert_eq!(s.len(),N);assert_eq!(s.as_ptr(),ptr);}
 assert_eq!(v.len(),N);assert_eq!(v.capacity(),cap);assert_eq!(v.as_ptr(),ptr);
 kani::cover!(cap==N);kani::cover!(cap>N);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_capacity_raw_projection(){NBZ_project_capacity([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()],kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_capacity_weight_projection(){NBZ_project_capacity([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}],kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_capacity_line_projection(){NBZ_project_capacity([M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_capacity_inverse_projection(){NBZ_project_capacity([[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]],kani::any());}

static mut NBZ_ROW_PTR:*const [u64;4]=core::ptr::null();
static mut NBZ_ROW_FLUSH:bool=false;
static mut NBZ_ROW_POWER:K=K::ZERO;
static mut NBZ_ROW_BASIS:M31=M31::ZERO;
static mut NBZ_ROW_REPLY:[u64;4]=[0;4];
static mut NBZ_ROW_CALLS:usize=0;
fn NBZ_update(row:&mut[u64;4],power:K,basis:M31,flush:bool) {unsafe {
 assert_eq!(NBZ_ROW_CALLS,0);NBZ_ROW_CALLS=1;assert_eq!(row as *const _,NBZ_ROW_PTR);
 assert_eq!(flush,NBZ_ROW_FLUSH);assert_eq!(basis,NBZ_ROW_BASIS);
 let k=NBZ_COORD%4;let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];
 assert_eq!(words(power)[k],words(NBZ_ROW_POWER)[k]);*row=NBZ_ROW_REPLY;}}
// Frozen BatchedWeights::push body with its native Vec slice projection
// factored at the dereference cut, and all other expressions unchanged.
fn NBZ_push_borrowed(raw:&mut[[u64;4]],terms:usize,index:usize,power:K,basis:M31) {
 let flush=terms&3==3;
 update_residue_row(&mut raw[index],power,basis,flush);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::update_residue_row,NBZ_update)]
fn NBZ_borrowed_push_frame() {
 let mut raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let terms:usize=kani::any();let i:usize=kani::any();kani::assume(i<64);
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=raw[j][k];let power=K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}};let basis=M31(kani::any());let reply:[u64;4]=kani::any();
 unsafe{NBZ_ROW_PTR=raw.as_ptr().add(i);NBZ_ROW_FLUSH=terms&3==3;NBZ_ROW_POWER=power;NBZ_ROW_BASIS=basis;NBZ_ROW_REPLY=reply;NBZ_COORD=k;}
 NBZ_push_borrowed(&mut raw,terms,i,power,basis);
 assert_eq!(raw[j][k],if i==j {reply[k]}else{before});unsafe{assert_eq!(NBZ_ROW_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i!=j);kani::cover!(terms&3==3);kani::cover!(terms&3!=3);
}
static mut NBZ_REDUCE_INPUT:[u64;4]=[0;4];
static mut NBZ_REDUCE_OUTPUT:[u32;4]=[0;4];
static mut NBZ_REDUCE_CALLS:usize=0;
fn NBZ_reduce(x:u64)->M31 {unsafe {let i=NBZ_REDUCE_CALLS;assert!(i<4);NBZ_REDUCE_CALLS+=1;assert_eq!(x,NBZ_REDUCE_INPUT[i]);M31(NBZ_REDUCE_OUTPUT[i])}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reduce)]
fn NBZ_finish_one_store() {
 let raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};
 let mut out:[K;64]=[K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}];
 let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let before=words(out[j])[k];
 let returned:[u32;4]=kani::any();kani::assume(returned[0]<2147483647);kani::assume(returned[1]<2147483647);kani::assume(returned[2]<2147483647);kani::assume(returned[3]<2147483647);
 unsafe{NBZ_REDUCE_OUTPUT=returned;if i<64 {NBZ_REDUCE_INPUT=b.raw[i];}}
 {let mut iter=out.iter_mut().enumerate();if i>0 {let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 assert_eq!(words(out[j])[k],if i<64&&i==j {returned[k]}else{before});
 unsafe{assert_eq!(NBZ_REDUCE_CALLS,if i<64 {4}else{0});}
 assert_eq!(b.raw.len(),64);
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}

fn NBZ_never_line(_a:E,_v:[E;4],_i:&[M31;5])->E {panic!("reject must not reach line fold")}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(super::opening,NBZ_open)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_never_line)]
fn NBZ_actual_query_reject() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs:NBZ_any_e(),power:NBZ_any_e().c0(),next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:kani::any()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 kani::assume(folded!=values[(u%4)as usize]);
 let result=query_values(&proof,&p,a,&g,None,&geometry,pending);
 assert!(matches!(result,Err(Error::Query)));unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(u%4==0);kani::cover!(u%4==3);
}

static mut NBZ_MUL_CALLS:usize=0;
static mut NBZ_MUL_X:M31=M31::ZERO;
static mut NBZ_MUL_Y:M31=M31::ZERO;
static mut NBZ_MUL_OUT:M31=M31::ZERO;
static mut NBZ_PREPARED:*const Prepared=core::ptr::null();
static mut NBZ_INITIAL_WEIGHT:*const K=core::ptr::null();
static mut NBZ_INITIAL_RAW:*const[u64;4]=core::ptr::null();
static mut NBZ_INITIAL_RHS:E=E::ZERO;
static mut NBZ_INITIAL_POWER:K=K::ZERO;
static mut NBZ_OUTPUT:Option<(Accumulator,BatchedWeights)>=None;
fn NBZ_m31(x:M31,y:M31)->M31 {
 assert!(x.0<2147483647);assert!(y.0<2147483647);
 let out:u32=kani::any();kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);
 unsafe{NBZ_MUL_CALLS+=1;NBZ_MUL_X=x;NBZ_MUL_Y=y;NBZ_MUL_OUT=M31(out);}M31(out)
}
fn NBZ_full_line(alpha:E,values:[E;4],inverse:&[M31;5])->E {
 unsafe{assert_eq!(NBZ_EVENT,8);NBZ_EVENT=9;}NBZ_line(alpha,values,inverse)
}
fn NBZ_accumulate(p:&Prepared,a:&mut Accumulator,node:M31,value:E,pending:&mut BatchedWeights) {
 unsafe{
 assert_eq!(NBZ_EVENT,9);NBZ_EVENT=10;assert_eq!(p as *const _,NBZ_PREPARED);
 assert_eq!(a.weights.as_ptr(),NBZ_INITIAL_WEIGHT);assert_eq!(pending.raw.as_ptr(),NBZ_INITIAL_RAW);
 assert_eq!(a.weights.len(),64);assert_eq!(pending.raw.len(),64);assert_eq!(a.next,NBZ_Q);assert_eq!(pending.terms,a.next);
 let k=NBZ_COORD;assert_eq!(a.rhs.to_limbs()[k],NBZ_INITIAL_RHS.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(a.power)[k%4],words(NBZ_INITIAL_POWER)[k%4]);
 assert_eq!(value.to_limbs()[k],NBZ_LINE.to_limbs()[k]);
 assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X,NBZ_MUL_Y);
 assert_eq!(node,NBZ_MUL_OUT.double().sub(M31::ONE));
 let(out,bout)=NBZ_OUTPUT.take().unwrap();*a=out;*pending=bout;
 }
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(super::opening,NBZ_open)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_full_line)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_accumulate)]
fn NBZ_actual_query_accept() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);let start:usize=kani::any();kani::assume(start<=next);
 let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let alpha1=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,alpha1],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let z:u32=kani::any();kani::assume(z<2147483647);let mut zs=[M31::ZERO;10];zs[next-start]=M31(z);
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from(zs)};
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 let out_rhs=NBZ_any_e();let out_power=NBZ_any_e().c0();let out_next:usize=kani::any();let out_terms:usize=kani::any();
 let aout=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs:out_rhs,power:out_power,next:out_next};let bout=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:out_terms};
 let aptr=aout.weights.as_ptr();let bptr=bout.raw.as_ptr();let aword=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aselected=aword(aout.weights[j])[k%4];let bselected=bout.raw[j][k%4];
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;NBZ_ALPHA1=alpha1;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];NBZ_LINE=NBZ_any_e();
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=pending.raw.as_ptr();NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;NBZ_OUTPUT=Some((aout,bout));}
 kani::assume(folded==values[(u%4)as usize]);
 let(a,b)=query_values(&proof,&p,a,&g,None,&geometry,pending).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,out_next);assert_eq!(b.terms,out_terms);assert_eq!(a.rhs.to_limbs()[k],out_rhs.to_limbs()[k]);assert_eq!(aword(a.power)[k%4],aword(out_power)[k%4]);
 assert_eq!(aword(a.weights[j])[k%4],aselected);assert_eq!(b.raw[j][k%4],bselected);
 unsafe{assert_eq!(NBZ_EVENT,10);assert_eq!(NBZ_LINE_CALLS,1);assert_eq!(NBZ_MUL_X.0,z);assert_eq!(NBZ_MUL_Y.0,z);assert!(NBZ_OUTPUT.is_none());}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(start==next);kani::cover!(j==63);
}

// Actual continuation AFTER the pure scalar multiplication returns.
// square is that reached return, not a field-operation stub.
fn NBZ_after_square(p:&Prepared,mut a:Accumulator,mut pending:BatchedWeights,
 square:M31,folded:E,i:usize,obs:Observer)->Result<(Accumulator,BatchedWeights),Error>{
    let node = square.double().sub(M31::ONE);
    accumulate_batched_with_node(p, &mut a, node, folded, &mut pending);
    mark(obs, Phase::Query(i));
    Ok((a, pending))
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_accumulate)]
fn NBZ_after_square_context() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);let start:usize=kani::any();kani::assume(start<=next);
 let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let alpha1=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,alpha1],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let z:u32=kani::any();kani::assume(z<2147483647);let mut zs=[M31::ZERO;10];zs[next-start]=M31(z);
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from(zs)};
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 let out_rhs=NBZ_any_e();let out_power=NBZ_any_e().c0();let out_next:usize=kani::any();let out_terms:usize=kani::any();
 let aout=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs:out_rhs,power:out_power,next:out_next};let bout=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:out_terms};
 let aptr=aout.weights.as_ptr();let bptr=bout.raw.as_ptr();let aword=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aselected=aword(aout.weights[j])[k%4];let bselected=bout.raw[j][k%4];
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;NBZ_ALPHA1=alpha1;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];NBZ_LINE=NBZ_any_e();
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=pending.raw.as_ptr();NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;NBZ_OUTPUT=Some((aout,bout));}
 let square:u32=kani::any();kani::assume(square<2147483647);
 unsafe{NBZ_EVENT=9;NBZ_LINE_CALLS=1;NBZ_MUL_CALLS=1;NBZ_MUL_X=M31(z);NBZ_MUL_Y=M31(z);NBZ_MUL_OUT=M31(square);}
 let(a,b)=NBZ_after_square(&p,a,pending,M31(square),unsafe{NBZ_LINE},next,None).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,out_next);assert_eq!(b.terms,out_terms);assert_eq!(a.rhs.to_limbs()[k],out_rhs.to_limbs()[k]);assert_eq!(aword(a.power)[k%4],aword(out_power)[k%4]);
 assert_eq!(aword(a.weights[j])[k%4],aselected);assert_eq!(b.raw[j][k%4],bselected);
 unsafe{assert_eq!(NBZ_EVENT,10);assert_eq!(NBZ_LINE_CALLS,1);assert_eq!(NBZ_MUL_X.0,z);assert_eq!(NBZ_MUL_Y.0,z);assert!(NBZ_OUTPUT.is_none());}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(start==next);kani::cover!(j==63);
}

fn NBZ_full_proof_prefix_case(){
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;57607]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_EVENT=1;NBZ_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 let out=NBZ_prefix(&proof,&p,next,&g,&geometry);
 if folded!=values[(u%4)as usize] {assert!(matches!(out,Err(Error::Query)));}
 else {let(f,v,inv)=out.unwrap();assert_eq!(f.to_limbs()[k],folded.to_limbs()[k]);
 let j:usize=kani::any();kani::assume(j<4);assert_eq!(v[j].to_limbs()[k],values[j].to_limbs()[k]);
 unsafe{assert_eq!(inv[k%5],NBZ_INV[k%5]);}}
 unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(folded==values[(u%4)as usize]);kani::cover!(folded!=values[(u%4)as usize]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
fn NBZ_full_proof_prefix(){NBZ_full_proof_prefix_case()}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

fn NBZ_none_mark_native() {
 let i:usize=kani::any();kani::assume(i<10);
 mark(None,Phase::Query(i));
 kani::cover!(i==0);kani::cover!(i==9);
}

static mut NBZ_MARK_CALLS:usize=0;
fn NBZ_mark_none(obs:Observer,phase:Phase) {
 assert!(obs.is_none());
 match phase {Phase::Query(i)=>unsafe{assert_eq!(i,NBZ_Q);},_=>panic!("wrong phase")}
 unsafe{NBZ_MARK_CALLS+=1;}
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_accumulate)]
#[kani::stub(crate::verifier::mark,NBZ_mark_none)]
fn NBZ_after_square_checked_mark() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);let start:usize=kani::any();kani::assume(start<=next);
 let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let alpha1=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,alpha1],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let z:u32=kani::any();kani::assume(z<2147483647);let mut zs=[M31::ZERO;10];zs[next-start]=M31(z);
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from(zs)};
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 let out_rhs=NBZ_any_e();let out_power=NBZ_any_e().c0();let out_next:usize=kani::any();let out_terms:usize=kani::any();
 let aout=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs:out_rhs,power:out_power,next:out_next};let bout=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:out_terms};
 let aptr=aout.weights.as_ptr();let bptr=bout.raw.as_ptr();let aword=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aselected=aword(aout.weights[j])[k%4];let bselected=bout.raw[j][k%4];
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;NBZ_ALPHA1=alpha1;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];NBZ_LINE=NBZ_any_e();
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=pending.raw.as_ptr();NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;NBZ_OUTPUT=Some((aout,bout));}
 let square:u32=kani::any();kani::assume(square<2147483647);
 unsafe{NBZ_EVENT=9;NBZ_LINE_CALLS=1;NBZ_MUL_CALLS=1;NBZ_MUL_X=M31(z);NBZ_MUL_Y=M31(z);NBZ_MUL_OUT=M31(square);}
 let(a,b)=NBZ_after_square(&p,a,pending,M31(square),unsafe{NBZ_LINE},next,None).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,out_next);assert_eq!(b.terms,out_terms);assert_eq!(a.rhs.to_limbs()[k],out_rhs.to_limbs()[k]);assert_eq!(aword(a.power)[k%4],aword(out_power)[k%4]);
 assert_eq!(aword(a.weights[j])[k%4],aselected);assert_eq!(b.raw[j][k%4],bselected);
 unsafe{assert_eq!(NBZ_EVENT,10);assert_eq!(NBZ_LINE_CALLS,1);assert_eq!(NBZ_MUL_X.0,z);assert_eq!(NBZ_MUL_Y.0,z);assert!(NBZ_OUTPUT.is_none());}
 unsafe{assert_eq!(NBZ_MARK_CALLS,1);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(start==next);kani::cover!(j==63);
}

// Literal continuation AFTER the SAME accumulation call returns.
fn NBZ_after_accumulation(a:Accumulator,pending:BatchedWeights,i:usize,obs:Observer)->Result<(Accumulator,BatchedWeights),Error>{
 mark(obs,Phase::Query(i));
 Ok((a,pending))
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::mark,NBZ_mark_none)]
fn NBZ_return_carriers() {
 let i:usize=kani::any();kani::assume(i<10);let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let next:usize=kani::any();let terms:usize=kani::any();
 let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let b=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms};
 let aptr=a.weights.as_ptr();let bptr=b.raw.as_ptr();let acap=a.weights.capacity();let bcap=b.raw.capacity();
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aw=words(a.weights[j])[k%4];let bw=b.raw[j][k%4];
 unsafe{NBZ_Q=i;}
 let(a,b)=NBZ_after_accumulation(a,b,i,None).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.capacity(),acap);assert_eq!(b.raw.capacity(),bcap);
 assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);assert_eq!(a.next,next);assert_eq!(b.terms,terms);
 assert_eq!(a.rhs.to_limbs()[k],rhs.to_limbs()[k]);assert_eq!(words(a.power)[k%4],words(power)[k%4]);assert_eq!(words(a.weights[j])[k%4],aw);assert_eq!(b.raw[j][k%4],bw);
 unsafe{assert_eq!(NBZ_MARK_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==9);kani::cover!(j==0);kani::cover!(j==63);
}

static mut NBZ_DISPATCH_SQUARE:M31=M31::ZERO;
static mut NBZ_DISPATCH_CALLS:usize=0;
fn NBZ_accumulate_observe(p:&Prepared,a:&mut Accumulator,node:M31,value:E,b:&mut BatchedWeights){unsafe{
 assert_eq!(NBZ_DISPATCH_CALLS,0);NBZ_DISPATCH_CALLS=1;assert_eq!(p as *const _,NBZ_PREPARED);
 assert_eq!(a.weights.as_ptr(),NBZ_INITIAL_WEIGHT);assert_eq!(b.raw.as_ptr(),NBZ_INITIAL_RAW);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,NBZ_Q);assert_eq!(b.terms,NBZ_Q);assert_eq!(node,NBZ_DISPATCH_SQUARE.double().sub(M31::ONE));
 let k=NBZ_COORD;assert_eq!(value.to_limbs()[k],NBZ_LINE.to_limbs()[k]);assert_eq!(a.rhs.to_limbs()[k],NBZ_INITIAL_RHS.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(a.power)[k%4],words(NBZ_INITIAL_POWER)[k%4]);
}}
// Literal node/accumulation dispatch between the pure multiply-return and
// the actual accumulation-return cuts. There is no field multiplication.
fn NBZ_node_dispatch(p:&Prepared,a:&mut Accumulator,pending:&mut BatchedWeights,square:M31,folded:E){
 let node=square.double().sub(M31::ONE);
 accumulate_batched_with_node(p,a,node,folded,pending);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_accumulate_observe)]
fn NBZ_node_dispatch_context(){
 let next:usize=kani::any();kani::assume(next<10);let square:u32=kani::any();kani::assume(square<2147483647);
 let k:usize=kani::any();kani::assume(k<8);let line=NBZ_any_e();let rhs=NBZ_any_e();let power=NBZ_any_e().c0();
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let mut a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let mut b=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 unsafe{NBZ_Q=next;NBZ_COORD=k;NBZ_LINE=line;NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=b.raw.as_ptr();NBZ_DISPATCH_SQUARE=M31(square);}
 NBZ_node_dispatch(&p,&mut a,&mut b,M31(square),line);
 unsafe{assert_eq!(NBZ_DISPATCH_CALLS,1);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(square==0);kani::cover!(square==2147483646);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_never_line)]
fn NBZ_full_proof_actual_reject() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;57607]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::from([[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]]),line_z:Vec::from([M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())])};
 let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs:NBZ_any_e(),power:NBZ_any_e().c0(),next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:kani::any()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_EVENT=1;NBZ_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 kani::assume(folded!=values[(u%4)as usize]);
 let result=query_values(&proof,&p,a,&g,None,&geometry,pending);
 assert!(matches!(result,Err(Error::Query)));unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(u%4==0);kani::cover!(u%4==3);
}

// The extra canonical-output assumption is redundant by the paired emitted
// m31_value theorem. The exact natural multiplication spec remains present.
fn NBZ_m31_canonical_reply(x:M31,y:M31)->M31 {
 assert!(x.0<2147483647);assert!(y.0<2147483647);
 let out:u32=kani::any();kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);kani::assume(out<2147483647);
 unsafe{NBZ_MUL_CALLS+=1;NBZ_MUL_X=x;NBZ_MUL_Y=y;NBZ_MUL_OUT=M31(out);NBZ_DISPATCH_SQUARE=M31(out);}M31(out)
}
fn NBZ_forward_accumulate(p:&Prepared,a:&mut Accumulator,node:M31,value:E,b:&mut BatchedWeights){
 unsafe{assert_eq!(NBZ_EVENT,9);NBZ_EVENT=10;}NBZ_accumulate_observe(p,a,node,value,b)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_full_line)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31_canonical_reply)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_forward_accumulate)]
#[kani::stub(crate::verifier::mark,NBZ_mark_none)]
fn NBZ_full_proof_forward_calls() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);let start:usize=kani::any();kani::assume(start<=next);
 let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let alpha1=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,alpha1],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;57607]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let z:u32=kani::any();kani::assume(z<2147483647);let mut zs=[M31::ZERO;10];zs[next-start]=M31(z);
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from(zs)};
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let pending=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_EVENT=1;NBZ_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;NBZ_ALPHA1=alpha1;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];NBZ_LINE=NBZ_any_e();
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=pending.raw.as_ptr();NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;}
 kani::assume(folded==values[(u%4)as usize]);
 let result=query_values(&proof,&p,a,&g,None,&geometry,pending);
 assert!(matches!(result,Ok(_)));
 unsafe{assert_eq!(NBZ_EVENT,10);assert_eq!(NBZ_DISPATCH_CALLS,1);assert_eq!(NBZ_MARK_CALLS,1);assert_eq!(NBZ_LINE_CALLS,1);assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X.0,z);assert_eq!(NBZ_MUL_Y.0,z);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(start==next);kani::cover!(j==63);
}

static mut NBZ_SCALAR_CALLS:usize=0;
static mut NBZ_SCALAR_INPUT:[[u32;4];2]=[[0;4];2];
static mut NBZ_SCALAR_SCALE:[u32;2]=[0;2];
static mut NBZ_SCALAR_OUTPUT:[[u32;4];2]=[[0;4];2];
fn NBZ_qwords(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn NBZ_qfrom(w:[u32;4])->K {K{c0:aspis_core::field::CM31{a:M31(w[0]),b:M31(w[1])},c1:aspis_core::field::CM31{a:M31(w[2]),b:M31(w[3])}}}
fn NBZ_qscalar_spec(x:K,s:M31)->K {
 let w=NBZ_qwords(x);assert!(s.0<2147483647);assert!(w[0]<2147483647);assert!(w[1]<2147483647);assert!(w[2]<2147483647);assert!(w[3]<2147483647);
 let out:[u32;4]=kani::any();
 kani::assume(out[0]<2147483647);kani::assume(out[1]<2147483647);kani::assume(out[2]<2147483647);kani::assume(out[3]<2147483647);
 kani::assume(out[0]as u64==(w[0]as u64*s.0 as u64)%2147483647);
 kani::assume(out[1]as u64==(w[1]as u64*s.0 as u64)%2147483647);
 kani::assume(out[2]as u64==(w[2]as u64*s.0 as u64)%2147483647);
 kani::assume(out[3]as u64==(w[3]as u64*s.0 as u64)%2147483647);
 unsafe{let i=NBZ_SCALAR_CALLS;assert!(i<2);NBZ_SCALAR_CALLS+=1;NBZ_SCALAR_INPUT[i]=w;NBZ_SCALAR_SCALE[i]=s.0;NBZ_SCALAR_OUTPUT[i]=out;}
 NBZ_qfrom(out)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NBZ_qscalar_spec)]
fn NBZ_wide_scalar_dispatch(){
 let x=NBZ_any_e();let scalar:u32=kani::any();kani::assume(scalar<2147483647);let k:usize=kani::any();kani::assume(k<8);
 let y=x.mul_m31(M31(scalar));
 unsafe{assert_eq!(NBZ_SCALAR_CALLS,2);assert_eq!(NBZ_SCALAR_INPUT[k/4][k%4],x.to_limbs()[k]);assert_eq!(NBZ_SCALAR_SCALE[k/4],scalar);assert_eq!(y.to_limbs()[k],NBZ_SCALAR_OUTPUT[k/4][k%4]);}
 kani::cover!(k==0);kani::cover!(k==7);kani::cover!(scalar==0);kani::cover!(scalar==2147483646);
}

// ONE literal basis iteration on an arbitrary pre-state, including all other
//255 arbitrary cells. Copy bound covers the entire1024-byte basis backing.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31_canonical_reply)]
fn NBZ_basis_store_full_copy_bound(){
 let mut basis:[M31;256]=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let n:usize=kani::any();kani::assume(n>=1&&n<=128);
 let j:usize=kani::any();kani::assume(j<n);let i:usize=kani::any();kani::assume(i<256);
 let node:u32=kani::any();kani::assume(node<2147483647);kani::assume(basis[j].0<2147483647);
 let old=basis[i];let input=basis[j];
 basis[n+j]=basis[j].mul(M31(node));
 unsafe{assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X,input);assert_eq!(NBZ_MUL_Y.0,node);assert_eq!(basis[i],if i==n+j {NBZ_MUL_OUT}else{old});}
 kani::cover!(n==1);kani::cover!(n==128);kani::cover!(j==127);kani::cover!(i==n+j);kani::cover!(i!=n+j);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_range_next_bounded(){
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=256);kani::assume(end<=256);
 let mut iter=start..end;let result=iter.next();
 if start<end {assert_eq!(result,Some(start));assert_eq!(iter.start,start+1);}
 else {assert_eq!(result,None);assert_eq!(iter.start,start);}
 assert_eq!(iter.end,end);
 kani::cover!(start==0&&end==128);kani::cover!(start==end);kani::cover!(start>end);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_basis_initializer(){
 let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let n=1usize;
 let i:usize=kani::any();kani::assume(i<256);
 assert_eq!(basis[i],if i==0 {M31::ONE}else{M31::ZERO});assert_eq!(n,1);
 kani::cover!(i==0);kani::cover!(i==255);
}
// ONE outer post-inner continuation. The returned basis is not rebuilt.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31_canonical_reply)]
fn NBZ_basis_outer_after_inner(){
 let mut n:usize=kani::any();kani::assume(n>=1&&n<=32);let oldn=n;
 let mut node:u32=kani::any();kani::assume(node<2147483647);let oldnode=node;
 node=M31(node).mul(M31(node)).double().sub(M31::ONE).0;n*=2;
 assert_eq!(n,2*oldn);assert!(n<=64);assert!(node<2147483647);
 unsafe{assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X.0,oldnode);assert_eq!(NBZ_MUL_Y.0,oldnode);assert_eq!(node,NBZ_MUL_OUT.double().sub(M31::ONE).0);}
 kani::cover!(oldn==1);kani::cover!(oldn==32);
}

fn NBZ_any_q()->K {let w:[u32;4]=kani::any();kani::assume(w[0]<2147483647);kani::assume(w[1]<2147483647);kani::assume(w[2]<2147483647);kani::assume(w[3]<2147483647);NBZ_qfrom(w)}
static mut NBZ_ROW_TRACE_CALLS:usize=0;
static mut NBZ_ROW_TRACE_INDEX:usize=0;
static mut NBZ_ROW_WEIGHT_WORDS:[u32;4]=[0;4];
fn NBZ_row_trace(slot:u16,index:usize,value:E){unsafe{
 let call=NBZ_ROW_TRACE_CALLS;assert!(call<2);NBZ_ROW_TRACE_CALLS+=1;assert_eq!(index,NBZ_ROW_TRACE_INDEX);
 let k=NBZ_COORD;assert_eq!(slot,if call==0 {12}else{13});
 let expected=if call==0 {if k<4 {NBZ_ROW_WEIGHT_WORDS[k]}else{0}}else{if k==0 {NBZ_ROW_BASIS.0}else{0}};
 assert_eq!(value.to_limbs()[k],expected);
}}
// Frozen release ONE-row body. cfg(prover) is false in the adopted builds.
fn NBZ_row_body(a:&Accumulator,weights:&mut BatchedWeights,basis:&[M31;256],j:usize,width:usize){
 weights.push(j,a.power,basis_at(basis,j));
 crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
 crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(basis,j)));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::update_residue_row,NBZ_update)]
#[kani::stub(crate::trace::value,NBZ_row_trace)]
fn NBZ_full_row_body(){
 let next:usize=kani::any();kani::assume(next<10);let terms:usize=kani::any();let j:usize=kani::any();kani::assume(j<64);let i:usize=kani::any();kani::assume(i<64);let k:usize=kani::any();kani::assume(k<8);
 let a=Accumulator{weights:Vec::from([NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q(),NBZ_any_q()]),rhs:NBZ_any_e(),power:NBZ_any_q(),next};
 let mut weights=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms};let basis:[M31;256]=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];kani::assume(basis[j].0<2147483647);
 let reply:[u64;4]=kani::any();let old=weights.raw[i][k%4];let aptr=a.weights.as_ptr();let bptr=weights.raw.as_ptr();
 unsafe{NBZ_COORD=k;NBZ_ROW_PTR=weights.raw.as_ptr().add(j);NBZ_ROW_FLUSH=terms&3==3;NBZ_ROW_POWER=a.power;NBZ_ROW_BASIS=basis[j];NBZ_ROW_REPLY=reply;NBZ_ROW_TRACE_INDEX=next*64+j;NBZ_ROW_WEIGHT_WORDS=NBZ_qwords(a.weights[j]);}
 NBZ_row_body(&a,&mut weights,&basis,j,64);
 assert_eq!(weights.raw[i][k%4],if i==j {reply[k%4]}else{old});assert_eq!(weights.terms,terms);assert_eq!(weights.raw.len(),64);assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(weights.raw.as_ptr(),bptr);
 unsafe{assert_eq!(NBZ_ROW_CALLS,1);assert_eq!(NBZ_ROW_TRACE_CALLS,2);}
 kani::cover!(j==0);kani::cover!(j==63);kani::cover!(i!=j);kani::cover!(k==0);kani::cover!(k==7);
}
// ONE literal constructor while-body on arbitrary reached backing contents.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_initializer_borrowed_step(){
 let weights:[K;64]=[NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>())];let mut raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let mut index:usize=kani::any();kani::assume(index<=64);let old_index=index;
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);let before=raw[j][k];let mut chosen=0;
 if index<weights.len(){let w=weights[index];chosen=NBZ_qwords(w)[k]as u64;raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];index+=1;}
 assert_eq!(index,old_index+usize::from(old_index<64));assert_eq!(raw[j][k],if old_index<64&&old_index==j {chosen}else{before});
 kani::cover!(old_index==0);kani::cover!(old_index==63);kani::cover!(old_index==64);kani::cover!(old_index!=j);
}
static mut NBZ_FINISH_SELF:*const BatchedWeights=core::ptr::null();
static mut NBZ_FINISH_INDEX:usize=0;
static mut NBZ_FINISH_VALUE:K=K::ZERO;
static mut NBZ_FINISH_CALLS:usize=0;
fn NBZ_finish_value_reply(b:&BatchedWeights,index:usize)->K {unsafe{
 assert_eq!(b as *const _,NBZ_FINISH_SELF);assert_eq!(index,NBZ_FINISH_INDEX);assert_eq!(b.raw.len(),64);NBZ_FINISH_CALLS+=1;NBZ_FINISH_VALUE
}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::BatchedWeights::value,NBZ_finish_value_reply)]
fn NBZ_finish_vec_capacity_step(){
 let cap:usize=kani::any();kani::assume(cap>=64&&cap<=isize::MAX as usize/core::mem::size_of::<K>());
 let initial:[K;64]=[NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>())];let mut weights:Vec<K>=Vec::with_capacity(cap);weights.extend_from_slice(&initial);
 let b=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:kani::any()};let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=NBZ_qwords(weights[j])[k];let ptr=weights.as_ptr();let result=NBZ_any_q();
 unsafe{NBZ_FINISH_SELF=&b;NBZ_FINISH_INDEX=i;NBZ_FINISH_VALUE=result;}
 {let mut iter=weights.as_mut_slice().iter_mut().enumerate();if i>0{let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 assert_eq!(weights.as_ptr(),ptr);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),cap);assert_eq!(NBZ_qwords(weights[j])[k],if i<64&&i==j {NBZ_qwords(result)[k]}else{before});
 unsafe{assert_eq!(NBZ_FINISH_CALLS,if i<64{1}else{0});}
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}

const _: ()=assert!(!cfg!(feature="prover"));
static mut NBZ_SCALE_CALLS:usize=0;
static mut NBZ_SCALE_X:[u32;3]=[0;3];static mut NBZ_SCALE_Y:[u32;3]=[0;3];static mut NBZ_SCALE_OUT:[u32;3]=[0;3];
fn NBZ_scale_spec(x:M31,y:M31)->M31{
 assert!(x.0<2147483647);assert!(y.0<2147483647);let out:u32=kani::any();
 kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);kani::assume(out<2147483647);
 unsafe{let i=NBZ_SCALE_CALLS;assert!(i<3);NBZ_SCALE_CALLS+=1;NBZ_SCALE_X[i]=x.0;NBZ_SCALE_Y[i]=y.0;NBZ_SCALE_OUT[i]=out;}M31(out)
}
// Native pre-scalar cuts. Cases7/8 start AFTER the SAME c0/c1 scale calls:
// a,b are those returned canonical values, not the opening's original a,b.
fn NBZ_coefficient_cut(which:u8,a:E,b:E,c:E,d:E,inverse:[M31;5])->(E,M31){
 let quarter=M31(536870912);let half=M31(1073741824);
 match which{
 0=>(a.add(b).add(c).add(d),quarter),
 1=>(a.sub(b).sub(c).add(d),quarter.mul(inverse[1])),
 2=>(a.add(b).sub(c).sub(d),quarter.mul(inverse[0])),
 3=>(a.sub(b).add(c).sub(d),quarter.mul(inverse[0]).mul(inverse[1])),
 4=>(a.add(b).sub(c).sub(d),quarter.mul(inverse[4])),
 5=>(a.sub(b),half.mul(inverse[2])),
 6=>(d.sub(c),half.mul(inverse[3])),
 7=>(a.add(b),half),
 _=>(a.sub(b),half.mul(inverse[4]))
 }
}
fn NBZ_coefficient_case(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_eq!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_common_h0(){NBZ_coefficient_case(0);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h1(){NBZ_coefficient_case(1);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h2(){NBZ_coefficient_case(2);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h3(){NBZ_coefficient_case(3);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h2(){NBZ_coefficient_case(4);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_c0(){NBZ_coefficient_case(5);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_c1(){NBZ_coefficient_case(6);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h1(){NBZ_coefficient_case(7);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h3(){NBZ_coefficient_case(8);}

// ONE Horner pre-multiply cut shared by all three source nesting sites.
fn NBZ_horner_argument(alpha:E,h:E,previous_product:E)->(E,E){(alpha,h.add(previous_product))}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_horner_argument_cut(){
 let alpha=NBZ_any_e();let h=NBZ_any_e();let previous=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let(receiver,arg)=NBZ_horner_argument(alpha,h,previous);
 assert_eq!(receiver.to_limbs()[k],alpha.to_limbs()[k]);assert!(arg.to_limbs()[k]<2147483647);
 kani::cover!(k==0);kani::cover!(k==7);
}

// Exact field carrier/conversion cuts, no field multiplication executed.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(32)]
fn NBZ_compare_eight_coordinates(){
 let a=NBZ_any_e();let b=NBZ_any_e();let x=a.to_limbs();let y=b.to_limbs();
 let same=x[0]==y[0]&&x[1]==y[1]&&x[2]==y[2]&&x[3]==y[3]&&x[4]==y[4]&&x[5]==y[5]&&x[6]==y[6]&&x[7]==y[7];
 assert_eq!(a==b,same);assert_eq!(a!=b,!same);kani::cover!(same);kani::cover!(!same);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(32)]
fn NBZ_embed_q_domain(){
 let q=NBZ_any_q();let x=E::from_qm31(q);let w=NBZ_qwords(q);let k:usize=kani::any();kani::assume(k<8);
 assert_eq!(x.to_limbs()[k],if k<4{w[k]}else{0});kani::cover!(k==7);kani::cover!(k==0);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(32)]
fn NBZ_embed_m_domain(){
 let m:u32=kani::any();kani::assume(m<2147483647);let x=E::from_m31(M31(m));let k:usize=kani::any();kani::assume(k<8);
 assert_eq!(x.to_limbs()[k],if k==0{m}else{0});kani::cover!(k==7);kani::cover!(k==0);
}
// A single initialized destination window with arbitrary successful capacity.
// Whole-vector ownership/ordinal association is deliberately a separate row.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(32)]
fn NBZ_capacity_finish_window(){
 NBZ_capacity_raw_window_case();
 let cap:usize=kani::any();kani::assume(cap>=64&&cap<=isize::MAX as usize/core::mem::size_of::<K>());
 let old=NBZ_any_q();let reply=NBZ_any_q();let mut weights=Vec::<K>::with_capacity(cap);weights.push(old);let ptr=weights.as_ptr();
 let index:usize=kani::any();kani::assume(index<64);
 {let w=&mut weights.as_mut_slice()[0];*w=reply;}
 assert_eq!(weights[0],reply);assert_eq!(weights.len(),1);assert_eq!(weights.capacity(),cap);assert_eq!(weights.as_ptr(),ptr);
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(index==63);
}
// Literal one-row constructor write in a one-row slice window. The caller
// supplies the offset separately; no sparse whole-array prestate is assumed.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(32)]
fn NBZ_initializer_window(){
 let q=NBZ_any_q();let mut raw:[u64;4]=kani::any();let k:usize=kani::any();kani::assume(k<4);
 let w=q;raw=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
 assert_eq!(raw[k],NBZ_qwords(q)[k]as u64);kani::cover!(k==0);kani::cover!(k==3);
}

fn NBZ_capacity_raw_window_case(){
 let cap:usize=kani::any();kani::assume(cap>=64&&cap<=isize::MAX as usize/core::mem::size_of::<[u64;4]>());
 let old:[u64;4]=kani::any();let reply:[u64;4]=kani::any();let mut raw=Vec::<[u64;4]>::with_capacity(cap);raw.push(old);let ptr=raw.as_ptr();
 let k:usize=kani::any();kani::assume(k<4);let before=raw[0][k];assert_eq!(before,old[k]);
 {let row=&mut raw.as_mut_slice()[0];*row=reply;}
 assert_eq!(raw[0][k],reply[k]);assert_eq!(raw.len(),1);assert_eq!(raw.capacity(),cap);assert_eq!(raw.as_ptr(),ptr);
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(k==3);
}

// Inherited NBB one-step cuts, exact prefix rename plus KMX configuration.
use super::*;
use aspis_core::field::CM31;
static mut NBZ_NBB_OLD:[u64;4]=[0;4];
static mut NBZ_NBB_OUT:[u64;4]=[0;4];
static mut NBZ_NBB_POWER:[u32;4]=[0;4];
static mut NBZ_NBB_BASIS:u32=0;
static mut NBZ_NBB_FLUSH:bool=false;
static mut NBZ_NBB_CALLS:usize=0;

// Overapproximation of the row leaf; NBZ_NBB_Row.source proves totality and the
// unique actual value on the caller's phase/canonical domain. No multiply runs.
fn NBZ_NBB_row_reply(row:&mut[u64;4],power:K,basis:M31,flush:bool) {
    unsafe {
        NBZ_NBB_OLD=*row;
        NBZ_NBB_POWER=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        NBZ_NBB_BASIS=basis.0;NBZ_NBB_FLUSH=flush;NBZ_NBB_CALLS+=1;
        let out:[u64;4]=kani::any();NBZ_NBB_OUT=out;*row=out;
    }
}
fn NBZ_NBB_add(old:u64,limb:u32,basis:M31)->u64 {old+u64::from(limb)*u64::from(basis.0)}
static mut NBZ_NBB_RAW:u64=0;
static mut NBZ_NBB_LIMB:u32=0;
static mut NBZ_NBB_REPLY:u64=0;
fn NBZ_NBB_add_reply(old:u64,limb:u32,basis:M31)->u64 {
    unsafe {NBZ_NBB_RAW=old;NBZ_NBB_LIMB=limb;NBZ_NBB_BASIS=basis.0;let out=kani::any();NBZ_NBB_REPLY=out;out}
}
// Literal one-iteration body, factoring only the checked integer scalar leaf.
fn NBZ_NBB_add_iteration(row:&mut[u64;4],limbs:&[u32;4],basis:M31,j:usize) {
    let old=residue_limb_at(row,j);
    let limb=power_limb_at(limbs,j);
    row[j]=NBZ_NBB_add(old,limb,basis);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(NBZ_NBB_add,NBZ_NBB_add_reply)]
fn NBZ_NBB_add_frame() {
    let mut row:[u64;4]=kani::any();let limbs:[u32;4]=kani::any();
    let j:usize=kani::any();kani::assume(j<4);
    let k:usize=kani::any();kani::assume(k<4);
    let basis:u32=kani::any();let old=row[j];let before=row[k];
    NBZ_NBB_add_iteration(&mut row,&limbs,M31(basis),j);
    unsafe {assert_eq!(NBZ_NBB_RAW,old);assert_eq!(NBZ_NBB_LIMB,limbs[j]);assert_eq!(NBZ_NBB_BASIS,basis);
        assert_eq!(row[k],if k==j {NBZ_NBB_REPLY} else {before});}
    kani::cover!(j==0);kani::cover!(j==3);kani::cover!(j!=k);
}
fn NBZ_NBB_fold(value:u64)->u64 {(value&0x7fff_ffff)+(value>>31)}
fn NBZ_NBB_fold_reply(value:u64)->u64 {
    unsafe {NBZ_NBB_RAW=value;let out=kani::any();NBZ_NBB_REPLY=out;out}
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(5)]
#[kani::stub(NBZ_NBB_fold,NBZ_NBB_fold_reply)]
fn NBZ_NBB_fold_frame() {
    let mut row:[u64;4]=kani::any();let before=row;
    let j:usize=kani::any();kani::assume(j<4);
    let k:usize=kani::any();kani::assume(k<4);
    let mut it=row.iter_mut();
    for _ in 0..j {let _=it.next().unwrap();}
    let limb=it.next().unwrap();*limb=NBZ_NBB_fold(*limb);
    unsafe {assert_eq!(NBZ_NBB_RAW,before[j]);assert_eq!(row[k],if j==k {NBZ_NBB_REPLY} else {before[k]});}
    kani::cover!(j==0);kani::cover!(j==3);kani::cover!(j!=k);
}

// The native continuation after Vec's checked indexed borrow. The Vec borrow
// itself uses the retained standard-library interpretation; no64-row loop runs.
fn NBZ_NBB_push_selected(row:&mut[u64;4],terms:usize,power:K,basis:M31) {
    let flush=terms&3==3;
    update_residue_row(row,power,basis,flush);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(super::update_residue_row,NBZ_NBB_row_reply)]
fn NBZ_NBB_push_selected_frame() {
    let mut row:[u64;4]=kani::any();let before=row;
    let p:[u32;4]=kani::any();let basis:u32=kani::any();let terms:usize=kani::any();
    let limb:usize=kani::any();kani::assume(limb<4);
    let power=K{c0:CM31{a:M31(p[0]),b:M31(p[1])},c1:CM31{a:M31(p[2]),b:M31(p[3])}};
    NBZ_NBB_push_selected(&mut row,terms,power,M31(basis));
    unsafe {
        assert_eq!(NBZ_NBB_CALLS,1);assert_eq!(NBZ_NBB_OLD[limb],before[limb]);
        assert_eq!(NBZ_NBB_POWER[limb],p[limb]);assert_eq!(NBZ_NBB_BASIS,basis);
        assert_eq!(NBZ_NBB_FLUSH,terms&3==3);assert_eq!(row[limb],NBZ_NBB_OUT[limb]);
    }
    kani::cover!(terms&3==3);kani::cover!(terms&3!=3);
}


// NBZ matched negative controls; positive definitions above are unchanged.
fn NBZ_prefix_case_negative(){
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_PROOF=proof.as_ptr();NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 let out=NBZ_prefix(&proof,&p,next,&g,&geometry);
 if folded!=values[(u%4)as usize] {assert!(matches!(out,Err(Error::Query)));}
 else {let(f,v,inv)=out.unwrap();assert_eq!(f.to_limbs()[k],folded.to_limbs()[k]);
 let j:usize=kani::any();kani::assume(j<4);assert_ne!(v[j].to_limbs()[k],values[j].to_limbs()[k]);
 unsafe{assert_eq!(inv[k%5],NBZ_INV[k%5]);}}
 unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(folded==values[(u%4)as usize]);kani::cover!(folded!=values[(u%4)as usize]);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
#[kani::stub(super::opening,NBZ_open)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
fn NBZ_prefix_all_g_negative(){NBZ_prefix_case_negative()}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBZ_line)]
fn NBZ_line_geometry_routing_negative() {
 let i:usize=kani::any();kani::assume(i<10);let start:usize=kani::any();kani::assume(start<=i);
 let k:usize=kani::any();kani::assume(k<8);let alpha=NBZ_any_e();let line=NBZ_any_e();
 let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let inverse=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let zs:[u32;10]=kani::any();
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from([
 M31(zs[0]),M31(zs[1]),M31(zs[2]),M31(zs[3]),M31(zs[4]),M31(zs[5]),M31(zs[6]),M31(zs[7]),M31(zs[8]),M31(zs[9])])};
 unsafe{NBZ_COORD=k;NBZ_ALPHA1=alpha;NBZ_LINE=line;NBZ_VALUES=values;NBZ_INV=inverse;}
 let(out,z)=NBZ_line_geometry(alpha,values,&inverse,i,&geometry);
 assert_eq!(out.to_limbs()[k],line.to_limbs()[k]);assert_ne!(z.0,zs[i-start]);
 assert_eq!(geometry.start,start);assert_eq!(geometry.line_z.len(),10);
 unsafe{assert_eq!(NBZ_LINE_CALLS,1);}
 kani::cover!(start==i);kani::cover!(i==9);kani::cover!(start<i);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(1024)]
fn NBZ_tail_assignment_negative() {
 let mut next:usize=kani::any();kani::assume(next<10);let mut terms:usize=kani::any();kani::assume(terms==next);
 let old=next;let mut rhs=NBZ_any_e();let old_rhs=rhs;let returned_rhs=NBZ_any_e();
 let mut power=K::ZERO;let returned_power=NBZ_any_e().c0();let k:usize=kani::any();kani::assume(k<8);
 terms+=1;
 assert_eq!(rhs.to_limbs()[k],old_rhs.to_limbs()[k]);
 rhs=returned_rhs;crate::trace::value(11,next,rhs);
 power=returned_power;next+=1;
 assert_eq!(next,old+1);assert_eq!(terms,next);assert_ne!(rhs.to_limbs()[k],returned_rhs.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(power)[k%4],words(returned_power)[k%4]);
 kani::cover!(old==0);kani::cover!(old==9);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::update_residue_row,NBZ_update)]
fn NBZ_borrowed_push_frame_negative() {
 let mut raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let terms:usize=kani::any();let i:usize=kani::any();kani::assume(i<64);
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=raw[j][k];let power=K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}};let basis=M31(kani::any());let reply:[u64;4]=kani::any();
 unsafe{NBZ_ROW_PTR=raw.as_ptr().add(i);NBZ_ROW_FLUSH=terms&3==3;NBZ_ROW_POWER=power;NBZ_ROW_BASIS=basis;NBZ_ROW_REPLY=reply;NBZ_COORD=k;}
 NBZ_push_borrowed(&mut raw,terms,i,power,basis);
 assert_ne!(raw[j][k],if i==j {reply[k]}else{before});unsafe{assert_eq!(NBZ_ROW_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i!=j);kani::cover!(terms&3==3);kani::cover!(terms&3!=3);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reduce)]
fn NBZ_finish_one_store_negative() {
 let raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};
 let mut out:[K;64]=[K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}];
 let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let before=words(out[j])[k];
 let returned:[u32;4]=kani::any();kani::assume(returned[0]<2147483647);kani::assume(returned[1]<2147483647);kani::assume(returned[2]<2147483647);kani::assume(returned[3]<2147483647);
 unsafe{NBZ_REDUCE_OUTPUT=returned;if i<64 {NBZ_REDUCE_INPUT=b.raw[i];}}
 {let mut iter=out.iter_mut().enumerate();if i>0 {let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 assert_ne!(words(out[j])[k],if i<64&&i==j {returned[k]}else{before});
 unsafe{assert_eq!(NBZ_REDUCE_CALLS,if i<64 {4}else{0});}
 assert_eq!(b.raw.len(),64);
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}

fn NBZ_full_proof_prefix_case_negative(){
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBZ_any_e();let folded=NBZ_any_e();let values=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBZ_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;57607]=kani::any();let g:[E;29]=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 unsafe {NBZ_Q=next;NBZ_COORD=k;NBZ_EVENT=1;NBZ_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);NBZ_G=g.as_ptr();NBZ_GEOM=&geometry;NBZ_ALPHA=alpha;
 NBZ_DOTS=[NBZ_any_e(),NBZ_any_e(),NBZ_any_e(),NBZ_any_e()];
 NBZ_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBZ_FOLD=folded;NBZ_VALUES=values;}
 let out=NBZ_prefix(&proof,&p,next,&g,&geometry);
 if folded!=values[(u%4)as usize] {assert!(matches!(out,Err(Error::Query)));}
 else {let(f,v,inv)=out.unwrap();assert_eq!(f.to_limbs()[k],folded.to_limbs()[k]);
 let j:usize=kani::any();kani::assume(j<4);assert_ne!(v[j].to_limbs()[k],values[j].to_limbs()[k]);
 unsafe{assert_eq!(inv[k%5],NBZ_INV[k%5]);}}
 unsafe{assert_eq!(NBZ_EVENT,8);}
 kani::cover!(folded==values[(u%4)as usize]);kani::cover!(folded!=values[(u%4)as usize]);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBZ_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBZ_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBZ_circle)]
#[kani::stub(crate::weights::field,NBZ_field)]
fn NBZ_full_proof_prefix_negative(){NBZ_full_proof_prefix_case_negative()}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::mark,NBZ_mark_none)]
fn NBZ_return_carriers_negative() {
 let i:usize=kani::any();kani::assume(i<10);let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let rhs=NBZ_any_e();let power=NBZ_any_e().c0();let next:usize=kani::any();let terms:usize=kani::any();
 let a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let b=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms};
 let aptr=a.weights.as_ptr();let bptr=b.raw.as_ptr();let acap=a.weights.capacity();let bcap=b.raw.capacity();
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aw=words(a.weights[j])[k%4];let bw=b.raw[j][k%4];
 unsafe{NBZ_Q=i;}
 let(a,b)=NBZ_after_accumulation(a,b,i,None).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.capacity(),acap);assert_eq!(b.raw.capacity(),bcap);
 assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);assert_eq!(a.next,next);assert_eq!(b.terms,terms);
 assert_eq!(a.rhs.to_limbs()[k],rhs.to_limbs()[k]);assert_eq!(words(a.power)[k%4],words(power)[k%4]);assert_ne!(words(a.weights[j])[k%4],aw);assert_eq!(b.raw[j][k%4],bw);
 unsafe{assert_eq!(NBZ_MARK_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==9);kani::cover!(j==0);kani::cover!(j==63);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBZ_accumulate_observe)]
fn NBZ_node_dispatch_context_negative(){
 let next:usize=kani::any();kani::assume(next<10);let square:u32=kani::any();kani::assume(square<2147483647);
 let k:usize=kani::any();kani::assume(k<8);let line=NBZ_any_e();let rhs=NBZ_any_e();let power=NBZ_any_e().c0();
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let mut a=Accumulator{weights:Vec::from([K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}},K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}]),rhs,power,next};
 let mut b=BatchedWeights{raw:Vec::from([kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()]),terms:next};
 unsafe{NBZ_Q=next;NBZ_COORD=k;NBZ_LINE=line;NBZ_INITIAL_RHS=rhs;NBZ_INITIAL_POWER=power;NBZ_PREPARED=&p;NBZ_INITIAL_WEIGHT=a.weights.as_ptr();NBZ_INITIAL_RAW=b.raw.as_ptr();NBZ_DISPATCH_SQUARE=M31(square);}
 NBZ_node_dispatch(&p,&mut a,&mut b,M31(square),line);
 unsafe{assert_eq!(NBZ_DISPATCH_CALLS,2);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(square==0);kani::cover!(square==2147483646);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NBZ_qscalar_spec)]
fn NBZ_wide_scalar_dispatch_negative(){
 let x=NBZ_any_e();let scalar:u32=kani::any();kani::assume(scalar<2147483647);let k:usize=kani::any();kani::assume(k<8);
 let y=x.mul_m31(M31(scalar));
 unsafe{assert_eq!(NBZ_SCALAR_CALLS,2);assert_eq!(NBZ_SCALAR_INPUT[k/4][k%4],x.to_limbs()[k]);assert_eq!(NBZ_SCALAR_SCALE[k/4],scalar);assert_ne!(y.to_limbs()[k],NBZ_SCALAR_OUTPUT[k/4][k%4]);}
 kani::cover!(k==0);kani::cover!(k==7);kani::cover!(scalar==0);kani::cover!(scalar==2147483646);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31_canonical_reply)]
fn NBZ_basis_store_full_copy_bound_negative(){
 let mut basis:[M31;256]=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let n:usize=kani::any();kani::assume(n>=1&&n<=128);
 let j:usize=kani::any();kani::assume(j<n);let i:usize=kani::any();kani::assume(i<256);
 let node:u32=kani::any();kani::assume(node<2147483647);kani::assume(basis[j].0<2147483647);
 let old=basis[i];let input=basis[j];
 basis[n+j]=basis[j].mul(M31(node));
 unsafe{assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X,input);assert_eq!(NBZ_MUL_Y.0,node);assert_ne!(basis[i],if i==n+j {NBZ_MUL_OUT}else{old});}
 kani::cover!(n==1);kani::cover!(n==128);kani::cover!(j==127);kani::cover!(i==n+j);kani::cover!(i!=n+j);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_range_next_bounded_negative(){
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=256);kani::assume(end<=256);
 let mut iter=start..end;let result=iter.next();
 if start<end {assert_eq!(result,Some(start));assert_eq!(iter.start,start+1);}
 else {assert_eq!(result,None);assert_eq!(iter.start,start);}
 assert_ne!(iter.end,end);
 kani::cover!(start==0&&end==128);kani::cover!(start==end);kani::cover!(start>end);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_basis_initializer_negative(){
 let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let n=1usize;
 let i:usize=kani::any();kani::assume(i<256);
 assert_ne!(basis[i],if i==0 {M31::ONE}else{M31::ZERO});assert_eq!(n,1);
 kani::cover!(i==0);kani::cover!(i==255);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_m31_canonical_reply)]
fn NBZ_basis_outer_after_inner_negative(){
 let mut n:usize=kani::any();kani::assume(n>=1&&n<=32);let oldn=n;
 let mut node:u32=kani::any();kani::assume(node<2147483647);let oldnode=node;
 node=M31(node).mul(M31(node)).double().sub(M31::ONE).0;n*=2;
 assert_eq!(n,2*oldn);assert!(n<=64);assert!(node<2147483647);
 unsafe{assert_eq!(NBZ_MUL_CALLS,1);assert_eq!(NBZ_MUL_X.0,oldnode);assert_eq!(NBZ_MUL_Y.0,oldnode);assert_ne!(node,NBZ_MUL_OUT.double().sub(M31::ONE).0);}
 kani::cover!(oldn==1);kani::cover!(oldn==32);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_initializer_borrowed_step_negative(){
 let weights:[K;64]=[NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>()),NBZ_qfrom(kani::any::<[u32;4]>())];let mut raw:[[u64;4];64]=[kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>(),kani::any::<[u64;4]>()];let mut index:usize=kani::any();kani::assume(index<=64);let old_index=index;
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);let before=raw[j][k];let mut chosen=0;
 if index<weights.len(){let w=weights[index];chosen=NBZ_qwords(w)[k]as u64;raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];index+=1;}
 assert_eq!(index,old_index+usize::from(old_index<64));assert_ne!(raw[j][k],if old_index<64&&old_index==j {chosen}else{before});
 kani::cover!(old_index==0);kani::cover!(old_index==63);kani::cover!(old_index==64);kani::cover!(old_index!=j);
}

fn NBZ_coeff_common_h0_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_ne!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_eq!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_common_h0_negative(){NBZ_coeff_common_h0_case_negative(0);}

fn NBZ_coeff_circle_h1_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h1_negative(){NBZ_coeff_circle_h1_case_negative(1);}

fn NBZ_coeff_circle_h2_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h2_negative(){NBZ_coeff_circle_h2_case_negative(2);}

fn NBZ_coeff_circle_h3_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_circle_h3_negative(){NBZ_coeff_circle_h3_case_negative(3);}

fn NBZ_coeff_line_h2_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h2_negative(){NBZ_coeff_line_h2_case_negative(4);}

fn NBZ_coeff_line_c0_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_c0_negative(){NBZ_coeff_line_c0_case_negative(5);}

fn NBZ_coeff_line_c1_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_c1_negative(){NBZ_coeff_line_c1_case_negative(6);}

fn NBZ_coeff_line_h1_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_ne!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_eq!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h1_negative(){NBZ_coeff_line_h1_case_negative(7);}

fn NBZ_coeff_line_h3_case_negative(which:u8){
 let a=NBZ_any_e();let b=NBZ_any_e();let c=NBZ_any_e();let d=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBZ_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBZ_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBZ_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBZ_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBZ_SCALE_X[1],NBZ_SCALE_OUT[0]);assert_eq!(NBZ_SCALE_Y[1],inv[1]);}
 assert_ne!(scale.0,NBZ_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBZ_scale_spec)]
fn NBZ_coeff_line_h3_negative(){NBZ_coeff_line_h3_case_negative(8);}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]

#[kani::unwind(4096)]
fn NBZ_horner_argument_cut_negative(){
 let alpha=NBZ_any_e();let h=NBZ_any_e();let previous=NBZ_any_e();let k:usize=kani::any();kani::assume(k<8);
 let(receiver,arg)=NBZ_horner_argument(alpha,h,previous);
 assert_ne!(receiver.to_limbs()[k],alpha.to_limbs()[k]);assert!(arg.to_limbs()[k]<2147483647);
 kani::cover!(k==0);kani::cover!(k==7);
}
