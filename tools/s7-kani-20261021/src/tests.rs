use super::*;
use support::*;
#[test]
fn geometry_all_ranges_and_invalid_inputs() {
 let queries=core::array::from_fn(|i|((i*11917+11)%262144) as u32);
 for start in 0..=23 {for end in 0..=23 {
  let a=QueryGeometry::for_range(&queries,start,end);let b=geometry_owned(queries,start,end);
  match (a,b) {(Ok(a),Ok(b))=>{assert_eq!(a.start,b.start);assert_eq!(a.inverses,b.inverses);assert_eq!(a.line_z,b.line_z);
   for i in start..end {let inv=a.for_query(i);let u=queries[i] as usize;let point=fast_domain::fibre_point(domain::FibreIndex::new(u).unwrap());assert_eq!(point.x.mul(inv[0]),M31::ONE);assert_eq!(point.y.mul(inv[1]),M31::ONE);}
  },(Err(a),Err(b))=>assert_eq!(a,b),_=>panic!("geometry mismatch")}
 }}
 let mut invalid=queries;invalid[11]=262144;
 assert!(matches!(geometry_owned(invalid,10,22),Err(Error::Query)));
 assert!(matches!(QueryGeometry::for_range(&invalid,10,22),Err(Error::Query)));
}
#[test]
fn real_width_accumulation_and_historical_modes() {
 let p=prepared([0;22]);
 for next in 0..22 {for phase in 0..4 {for node in [M31::ZERO,M31::ONE,M31(123456789),M31(2147483646)] {
  let a=Accumulator{weights:alloc::vec![K::ONE;64],rhs:E::ONE,power:K::ONE,next};
  let b=BatchedWeights{raw:alloc::vec![[1<<33;4];64],terms:phase};
  let mut shipped=copy_a(&a);let mut pending=copy_b(&b);
  accumulate_batched_with_node(&p,&mut shipped,node,E::ONE,&mut pending);
  let (owned,bowned)=accumulate_owned(&p,copy_a(&a),node,E::ONE,copy_b(&b));same(&shipped,&owned,&pending,&bowned);
  let mut historical=copy_a(&a);let mut bh=copy_b(&b);accumulate_with_node(&p,&mut historical,node,E::ONE,Some(&mut bh));
  let (reference,br)=accumulate_optional_owned(&p,copy_a(&a),node,E::ONE,Some(copy_b(&b)));same(&historical,&reference,&bh,&br.unwrap());
  let mut historical=copy_a(&a);accumulate_with_node(&p,&mut historical,node,E::ONE,None);
  let (reference,br)=accumulate_optional_owned(&p,copy_a(&a),node,E::ONE,None);
  same(&historical,&reference,&b,&b);assert!(br.is_none());
 }}}
}
#[test]
fn query_success_failure_and_offsets() {
 for start in [0,10] {for next in start..if start==0 {10}else{22} {
  let p=prepared(core::array::from_fn(|i|(i*11917%262144) as u32));
  let geometry=geometry_owned(p.queries,start,if start==0 {10}else{22}).unwrap();
  let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ONE,next};
  let b=BatchedWeights::new(&a.weights).unwrap();
  let mut proof=alloc::vec![0;compact::OFF_NODES];
  let g=[E::ZERO;29];
  let (s,t)=candidate::run(&proof,&p,copy_a(&a),&g,None,&geometry,copy_b(&b)).unwrap();
  let (u,v)=query_owned(&proof,&p,copy_a(&a),&g,None,&geometry,copy_b(&b)).unwrap();same(&s,&u,&t,&v);assert_eq!(s.next,next+1);
  let at=compact::OFF_OPENINGS+next*compact::OPENING+672+(p.queries[next] as usize%4)*32;proof[at]=1;
  assert!(matches!(candidate::run(&proof,&p,copy_a(&a),&g,None,&geometry,copy_b(&b)),Err(Error::Query)));
  assert!(matches!(query_owned(&proof,&p,a,&g,None,&geometry,b),Err(Error::Query)));
 }}
}
