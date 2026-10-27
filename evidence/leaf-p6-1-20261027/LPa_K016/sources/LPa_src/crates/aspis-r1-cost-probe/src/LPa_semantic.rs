//! Library calls, no child stubs. Owned boundary reference is XRg_boundary_reference.
use super::*;
fn canonical()->QM31{
 let x:[u32;4]=kani::any();kani::assume(x.iter().all(|x|*x<2147483647));
 QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(x[0]),aspis_core::field::M31(x[1])),c1:aspis_core::field::CM31::new(aspis_core::field::M31(x[2]),aspis_core::field::M31(x[3]))}
}
#[kani::proof] #[kani::unwind(30)] fn LPa_boundary(){
 let p:[QM31;28]=core::array::from_fn(|_|canonical());
 let mut r=p[0].add(p[0]);for i in 1..28{r=r.add(p[i]);}assert_eq!(semantic_boundary(&p),r);
}
// Reached decoder/storage stages with one arbitrary lane; remaining lanes zero.
// Full arbitrary87-lane/allocation association remains open.
fn claim_stage(point:usize){
 let mut bytes=[0u8;5+116*32];let q=canonical();let lane:usize=kani::any();kani::assume(lane<29);
 let at=5+(29*point+lane)*32;q.write_le_bytes(&mut bytes[at..at+16]);
 let p=crate::r1_wire::LPa_wire::prefix(&bytes);let actual=claims(&p).unwrap();
 let j:usize=kani::any();kani::assume(j<87);
 assert_eq!(actual[j/29][j%29],if j==29*point+lane{q}else{QM31::ZERO});
}
#[kani::proof] #[kani::unwind(32)] fn LPa_claim_point0(){claim_stage(0)}
#[kani::proof] #[kani::unwind(32)] fn LPa_claim_point2(){claim_stage(2)}
