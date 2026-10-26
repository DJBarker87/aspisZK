use aspis_core::field::{M31,CM31,QM31};
use aspis_statement::pool_v1::pair_forest_trace::{build_pool_v1_pair_forest_copy_registry_v1,PoolV1PairForestTraceV1};
use aspis_statement::pool_v1::pair_trace::{PoolV1PairCopyTupleV1,PoolV1PairTupleLimbV1,PoolV1PairTraceBankV1};
#[path="../../pv-rw-step/proof/generated.rs"] mod generated;
#[path="../../pv-rw-step/proof/iterator_state_step.rs"] mod combined;
fn limbs(q:QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn tuple(trace:&PoolV1PairForestTraceV1,tuple:PoolV1PairCopyTupleV1)->[M31;16] {
 tuple.limbs.map(|limb|match limb {
  PoolV1PairTupleLimbV1::Zero=>M31::ZERO,
  PoolV1PairTupleLimbV1::Cell{source,offset}=>{
   let columns=match source.bank {PoolV1PairTraceBankV1::Stable=>&trace.stable.c1,PoolV1PairTraceBankV1::Late=>&trace.late};
   columns[source.cell.column as usize][source.cell.row as usize].add(offset)
  }
 })
}
fn main() {
 let lambdas=[QM31::ZERO,QM31::ONE,QM31{c0:CM31::new(M31(7),M31(11)),c1:CM31::new(M31(17),M31(19))}];
 let registry=build_pool_v1_pair_forest_copy_registry_v1().unwrap();assert!(!registry.is_empty());
 for withdrawal in [false,true] {
  let fixture=aspis_prover::r0_fixture::prepare(withdrawal);
  let mut comparisons=0;let mut nonzero=0;
  for link in &registry { for source in [link.producer,link.consumer] {
   let values=tuple(&fixture.compiled.trace,source);
   if values.iter().any(|x|x.0!=0) {nonzero+=1;}
   for lambda in lambdas {
    let actual=aspis_statement::logup::compress_tagged_tuple(link.tag,&values,lambda);
    let copied=generated::compress_tagged_tuple(link.tag,&values,lambda);
    let reference=generated::reference16(link.tag,values,lambda);
    let mut state=(QM31::from_cm31(CM31::from_m31(link.tag)),lambda);
    let mut iterator=values.iter();let mut live_steps=0;
    loop {
     let (live,next,out,power)=combined::iterator_state_step(iterator,state.0,state.1,lambda);
     iterator=next;state=(out,power);
     if !live {break;}live_steps+=1;
    }
    assert_eq!(live_steps,16);assert!(iterator.as_slice().is_empty());
    assert_eq!(limbs(actual),limbs(copied));assert_eq!(limbs(actual),limbs(reference));assert_eq!(limbs(actual),limbs(state.0));
    let mut power=lambda;for _ in 0..16 {power=power.mul(lambda);}
    assert_eq!(limbs(state.1),limbs(power));comparisons+=1;
   }
  }}
  assert!(nonzero>0);
  let sample=tuple(&fixture.compiled.trace,registry[0].producer).map(|v|v.0);
  println!("{{\"fixture\":\"{}\",\"registry_links\":{},\"nonzero_tuples\":{},\"comparisons\":{},\"sample_tag\":{},\"sample_values\":{:?},\"lambda\":{:?},\"full_output_and_final_power_equal\":true}}",if withdrawal {"withdrawal"} else {"transfer"},registry.len(),nonzero,comparisons,registry[0].tag.0,sample,limbs(lambdas[2]));
 }
}
