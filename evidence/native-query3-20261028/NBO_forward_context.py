from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
s+='''
// The extra canonical-output assumption is redundant by the paired emitted
// m31_value theorem. The exact natural multiplication spec remains present.
fn NBO_m31_canonical_reply(x:M31,y:M31)->M31 {
 assert!(x.0<2147483647);assert!(y.0<2147483647);
 let out:u32=kani::any();kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);kani::assume(out<2147483647);
 unsafe{NBO_MUL_CALLS+=1;NBO_MUL_X=x;NBO_MUL_Y=y;NBO_MUL_OUT=M31(out);NBO_DISPATCH_SQUARE=M31(out);}M31(out)
}
fn NBO_forward_accumulate(p:&Prepared,a:&mut Accumulator,node:M31,value:E,b:&mut BatchedWeights){
 unsafe{assert_eq!(NBO_EVENT,9);NBO_EVENT=10;}NBO_accumulate_observe(p,a,node,value,b)
}
'''
a=s.index('fn NBO_actual_query_accept() {');b=s.index('\n}',a)+2
case=s[a:b].replace('fn NBO_actual_query_accept()', 'fn NBO_full_proof_forward_calls()')
# Remove the unused full post-state construction and observed-output checks:
start=case.index(' let out_rhs=');end=case.index(' unsafe {NBO_Q=',start)
case=case[:start]+case[end:]
case=case.replace('NBO_OUTPUT=Some((aout,bout));','')
case=case.replace('proof:[u8;832]','proof:[u8;57607]').replace('NBO_PROOF=proof.as_ptr();','NBO_EVENT=1;NBO_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);')
start=case.index(' let(a,b)=query_values');end=case.index(' kani::cover!',start)
case=case[:start]+''' let result=query_values(&proof,&p,a,&g,None,&geometry,pending);
 assert!(matches!(result,Ok(_)));
 unsafe{assert_eq!(NBO_EVENT,10);assert_eq!(NBO_DISPATCH_CALLS,1);assert_eq!(NBO_MARK_CALLS,1);assert_eq!(NBO_LINE_CALLS,1);assert_eq!(NBO_MUL_CALLS,1);assert_eq!(NBO_MUL_X.0,z);assert_eq!(NBO_MUL_Y.0,z);}
'''+case[end:]
s+='''#[kani::proof]
#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBO_full_line)]
#[kani::stub(aspis_core::field::M31::mul,NBO_m31_canonical_reply)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBO_forward_accumulate)]
#[kani::stub(crate::verifier::mark,NBO_mark_none)]
'''+case+'\n'
(E/'NBO_native.rs.txt').write_text(s)
