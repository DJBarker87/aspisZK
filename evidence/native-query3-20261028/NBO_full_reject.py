from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
s+='''
fn NBO_never_line(_a:E,_v:[E;4],_i:&[M31;5])->E {panic!("reject must not reach line fold")}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(super::opening,NBO_open)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBO_never_line)]
fn NBO_actual_query_reject() {
 let next:usize=kani::any();kani::assume(next<10);let u:u32=kani::any();kani::assume(u<262144);
 let k:usize=kani::any();kani::assume(k<8);let mut queries=[0;22];queries[next]=u;
 let alpha=NBO_any_e();let folded=NBO_any_e();let values=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[alpha,NBO_any_e()],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let proof:[u8;832]=kani::any();let g:[E;29]=['''+','.join('NBO_any_e()' for _ in range(29))+'''];
 let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};
 let a=Accumulator{weights:Vec::from(['''+','.join(q() for _ in range(64))+''']),rhs:NBO_any_e(),power:NBO_any_e().c0(),next};
 let pending=BatchedWeights{raw:Vec::from(['''+','.join('kani::any::<[u64;4]>()' for _ in range(64))+''']),terms:kani::any()};
 unsafe {NBO_Q=next;NBO_COORD=k;NBO_PROOF=proof.as_ptr();NBO_G=g.as_ptr();NBO_GEOM=&geometry;NBO_ALPHA=alpha;
 NBO_DOTS=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 NBO_INV=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 NBO_FOLD=folded;NBO_VALUES=values;}
 kani::assume(folded!=values[(u%4)as usize]);
 let result=query_values(&proof,&p,a,&g,None,&geometry,pending);
 assert!(matches!(result,Err(Error::Query)));unsafe{assert_eq!(NBO_EVENT,8);}
 kani::cover!(next==0);kani::cover!(next==9);kani::cover!(u%4==0);kani::cover!(u%4==3);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
