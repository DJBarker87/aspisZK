from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
weights='Vec::from(['+','.join(q() for _ in range(64))+'])'
raw='Vec::from(['+','.join('kani::any::<[u64;4]>()' for _ in range(64))+'])'
s+='''
static mut NBO_MUL_CALLS:usize=0;
static mut NBO_MUL_X:M31=M31::ZERO;
static mut NBO_MUL_Y:M31=M31::ZERO;
static mut NBO_MUL_OUT:M31=M31::ZERO;
static mut NBO_PREPARED:*const Prepared=core::ptr::null();
static mut NBO_INITIAL_WEIGHT:*const K=core::ptr::null();
static mut NBO_INITIAL_RAW:*const[u64;4]=core::ptr::null();
static mut NBO_INITIAL_RHS:E=E::ZERO;
static mut NBO_INITIAL_POWER:K=K::ZERO;
static mut NBO_OUTPUT:Option<(Accumulator,BatchedWeights)>=None;
fn NBO_m31(x:M31,y:M31)->M31 {
 assert!(x.0<2147483647);assert!(y.0<2147483647);
 let out:u32=kani::any();kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);
 unsafe{NBO_MUL_CALLS+=1;NBO_MUL_X=x;NBO_MUL_Y=y;NBO_MUL_OUT=M31(out);}M31(out)
}
fn NBO_full_line(alpha:E,values:[E;4],inverse:&[M31;5])->E {
 unsafe{assert_eq!(NBO_EVENT,8);NBO_EVENT=9;}NBO_line(alpha,values,inverse)
}
fn NBO_accumulate(p:&Prepared,a:&mut Accumulator,node:M31,value:E,pending:&mut BatchedWeights) {
 unsafe{
 assert_eq!(NBO_EVENT,9);NBO_EVENT=10;assert_eq!(p as *const _,NBO_PREPARED);
 assert_eq!(a.weights.as_ptr(),NBO_INITIAL_WEIGHT);assert_eq!(pending.raw.as_ptr(),NBO_INITIAL_RAW);
 assert_eq!(a.weights.len(),64);assert_eq!(pending.raw.len(),64);assert_eq!(a.next,NBO_Q);assert_eq!(pending.terms,a.next);
 let k=NBO_COORD;assert_eq!(a.rhs.to_limbs()[k],NBO_INITIAL_RHS.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(a.power)[k%4],words(NBO_INITIAL_POWER)[k%4]);
 assert_eq!(value.to_limbs()[k],NBO_LINE.to_limbs()[k]);
 assert_eq!(NBO_MUL_CALLS,1);assert_eq!(NBO_MUL_X,NBO_MUL_Y);
 assert_eq!(node,NBO_MUL_OUT.double().sub(M31::ONE));
 let(out,bout)=NBO_OUTPUT.take().unwrap();*a=out;*pending=bout;
 }
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(super::opening,NBO_open)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBO_full_line)]
#[kani::stub(aspis_core::field::M31::mul,NBO_m31)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBO_accumulate)]
fn NBO_actual_query_accept() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);let start:usize=kani::any();kani::assume(start<=next);
 let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let mut queries=[0;22];queries[next]=u;
 let alpha=NBO_any_e();let alpha1=NBO_any_e();let folded=NBO_any_e();let values=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,alpha1],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=['''+','.join('NBO_any_e()' for _ in range(29))+'''];
 let z:u32=kani::any();kani::assume(z<2147483647);let mut zs=[M31::ZERO;10];zs[next-start]=M31(z);
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from(zs)};
 let rhs=NBO_any_e();let power=NBO_any_e().c0();let a=Accumulator{weights:'''+weights+''',rhs,power,next};
 let pending=BatchedWeights{raw:'''+raw+''',terms:next};
 let out_rhs=NBO_any_e();let out_power=NBO_any_e().c0();let out_next:usize=kani::any();let out_terms:usize=kani::any();
 let aout=Accumulator{weights:'''+weights+''',rhs:out_rhs,power:out_power,next:out_next};let bout=BatchedWeights{raw:'''+raw+''',terms:out_terms};
 let aptr=aout.weights.as_ptr();let bptr=bout.raw.as_ptr();let aword=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aselected=aword(aout.weights[j])[k%4];let bselected=bout.raw[j][k%4];
 unsafe {NBO_Q=next;NBO_COORD=k;NBO_PROOF=proof.as_ptr();NBO_G=g.as_ptr();NBO_GEOM=&geometry;NBO_ALPHA=alpha;NBO_ALPHA1=alpha1;
 NBO_DOTS=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];NBO_LINE=NBO_any_e();
 NBO_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBO_FOLD=folded;NBO_VALUES=values;NBO_PREPARED=&p;NBO_INITIAL_WEIGHT=a.weights.as_ptr();NBO_INITIAL_RAW=pending.raw.as_ptr();NBO_INITIAL_RHS=rhs;NBO_INITIAL_POWER=power;NBO_OUTPUT=Some((aout,bout));}
 kani::assume(folded==values[(u%4)as usize]);
 let(a,b)=query_values(&proof,&p,a,&g,None,&geometry,pending).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,out_next);assert_eq!(b.terms,out_terms);assert_eq!(a.rhs.to_limbs()[k],out_rhs.to_limbs()[k]);assert_eq!(aword(a.power)[k%4],aword(out_power)[k%4]);
 assert_eq!(aword(a.weights[j])[k%4],aselected);assert_eq!(b.raw[j][k%4],bselected);
 unsafe{assert_eq!(NBO_EVENT,10);assert_eq!(NBO_LINE_CALLS,1);assert_eq!(NBO_MUL_X.0,z);assert_eq!(NBO_MUL_Y.0,z);assert!(NBO_OUTPUT.is_none());}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(start==next);kani::cover!(j==63);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
