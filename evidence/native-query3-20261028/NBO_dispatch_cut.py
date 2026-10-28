from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
s+='''
static mut NBO_DISPATCH_SQUARE:M31=M31::ZERO;
static mut NBO_DISPATCH_CALLS:usize=0;
fn NBO_accumulate_observe(p:&Prepared,a:&mut Accumulator,node:M31,value:E,b:&mut BatchedWeights){unsafe{
 assert_eq!(NBO_DISPATCH_CALLS,0);NBO_DISPATCH_CALLS=1;assert_eq!(p as *const _,NBO_PREPARED);
 assert_eq!(a.weights.as_ptr(),NBO_INITIAL_WEIGHT);assert_eq!(b.raw.as_ptr(),NBO_INITIAL_RAW);assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);
 assert_eq!(a.next,NBO_Q);assert_eq!(b.terms,NBO_Q);assert_eq!(node,NBO_DISPATCH_SQUARE.double().sub(M31::ONE));
 let k=NBO_COORD;assert_eq!(value.to_limbs()[k],NBO_LINE.to_limbs()[k]);assert_eq!(a.rhs.to_limbs()[k],NBO_INITIAL_RHS.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(a.power)[k%4],words(NBO_INITIAL_POWER)[k%4]);
}}
// Literal node/accumulation dispatch between the pure multiply-return and
// the actual accumulation-return cuts. There is no field multiplication.
fn NBO_node_dispatch(p:&Prepared,a:&mut Accumulator,pending:&mut BatchedWeights,square:M31,folded:E){
 let node=square.double().sub(M31::ONE);
 accumulate_batched_with_node(p,a,node,folded,pending);
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBO_accumulate_observe)]
fn NBO_node_dispatch_context(){
 let next:usize=kani::any();kani::assume(next<10);let square:u32=kani::any();kani::assume(square<2147483647);
 let k:usize=kani::any();kani::assume(k<8);let line=NBO_any_e();let rhs=NBO_any_e();let power=NBO_any_e().c0();
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let mut a=Accumulator{weights:Vec::from(['''+','.join(q() for _ in range(64))+''']),rhs,power,next};
 let mut b=BatchedWeights{raw:Vec::from(['''+','.join('kani::any::<[u64;4]>()' for _ in range(64))+''']),terms:next};
 unsafe{NBO_Q=next;NBO_COORD=k;NBO_LINE=line;NBO_INITIAL_RHS=rhs;NBO_INITIAL_POWER=power;NBO_PREPARED=&p;NBO_INITIAL_WEIGHT=a.weights.as_ptr();NBO_INITIAL_RAW=b.raw.as_ptr();NBO_DISPATCH_SQUARE=M31(square);}
 NBO_node_dispatch(&p,&mut a,&mut b,M31(square),line);
 unsafe{assert_eq!(NBO_DISPATCH_CALLS,1);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(square==0);kani::cover!(square==2147483646);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
