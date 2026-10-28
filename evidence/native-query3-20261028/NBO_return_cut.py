from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
s+='''
// Literal continuation AFTER the SAME accumulation call returns.
fn NBO_after_accumulation(a:Accumulator,pending:BatchedWeights,i:usize,obs:Observer)->Result<(Accumulator,BatchedWeights),Error>{
 mark(obs,Phase::Query(i));
 Ok((a,pending))
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::mark,NBO_mark_none)]
fn NBO_return_carriers() {
 let i:usize=kani::any();kani::assume(i<10);let k:usize=kani::any();kani::assume(k<8);let j:usize=kani::any();kani::assume(j<64);
 let rhs=NBO_any_e();let power=NBO_any_e().c0();let next:usize=kani::any();let terms:usize=kani::any();
 let a=Accumulator{weights:Vec::from(['''+','.join(q() for _ in range(64))+''']),rhs,power,next};
 let b=BatchedWeights{raw:Vec::from(['''+','.join('kani::any::<[u64;4]>()' for _ in range(64))+''']),terms};
 let aptr=a.weights.as_ptr();let bptr=b.raw.as_ptr();let acap=a.weights.capacity();let bcap=b.raw.capacity();
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let aw=words(a.weights[j])[k%4];let bw=b.raw[j][k%4];
 unsafe{NBO_Q=i;}
 let(a,b)=NBO_after_accumulation(a,b,i,None).unwrap();
 assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(a.weights.capacity(),acap);assert_eq!(b.raw.capacity(),bcap);
 assert_eq!(a.weights.len(),64);assert_eq!(b.raw.len(),64);assert_eq!(a.next,next);assert_eq!(b.terms,terms);
 assert_eq!(a.rhs.to_limbs()[k],rhs.to_limbs()[k]);assert_eq!(words(a.power)[k%4],words(power)[k%4]);assert_eq!(words(a.weights[j])[k%4],aw);assert_eq!(b.raw[j][k%4],bw);
 unsafe{assert_eq!(NBO_MARK_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==9);kani::cover!(j==0);kani::cover!(j==63);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
