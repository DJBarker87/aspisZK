#[cfg(all(test,aeneas_ref))]
mod tail_tests21 {
 use super::*;
 use crate::transcript::control21::Policy;
 struct Actual;
 impl Policy for Actual {
  fn gamma(b:&[u8;32])->E {crate::sampler::gamma_sample(b)}
  fn ordinary(b:&[u8;32])->E {crate::sampler::ordinary_sample(b)}
  fn qm31(b:&[u8;32])->K {crate::sampler::qm31_sample(b)}
  fn queries(b:&[[u8;32];8],a:&[[u8;32];8])->Result<([u32;22],[u8;32]),Error> {
   aspis_core::r0_transcript::queries_from_pairs(b,a).map_err(|_|Error::Transcript)
  }
 }
 #[derive(Clone,Copy)]
 struct Recording<'a> {log:&'a RefCell<Vec<(Vec<u8>,[u8;32])>>,zero:bool}
 impl Digest32 for Recording<'_> {
  fn digest(&self,parts:&[&[u8]])->[u8;32] {
   let out=if self.zero {[0;32]} else {HOST_HASH(parts)};
   self.log.borrow_mut().push((concat(parts),out));out
  }
 }
 fn compare(zero:bool) {
  let records=Records::placeholder().unwrap();let public=b"tail-control21-fixture";
  let a=RefCell::new(Vec::new());let b=RefCell::new(Vec::new());
  let left=Recording{log:&a,zero};let right=Recording{log:&b,zero};
  crate::trace::take();
  let original=walk(left,public,&records,Variant::S2);
  let native=crate::trace::take();
  let st=SemanticTranscript::new(right,public,&records.c1_root).unwrap();
  let (sem,mut st)=wire::semantic20::rows(st,records.semantic.clone(),0,[K::ZERO;25]);
  let sem=sem.unwrap();
  let z0=st.challenge_reference_circle_point(25,&records.semantic[25]).unwrap();
  let z1=st.challenge_reference_circle_point(26,&records.semantic[26]).unwrap();
  let (owned,_,trace)=tail_control21::<_,Actual>(right,st.state(),sem,[[z0.x,z0.y],[z1.x,z1.y]],&records,Variant::S2);
  let owned=owned.map(|(sem,_,gamma,kappa,alpha0,alpha1,queries,rho)|Drawn{sem,z:[z0,z1],gamma,kappa,alpha0,alpha1,queries,rho});
  assert!(original==owned);
  let encoded:Vec<_>=trace.into_iter().map(|(t,i,v)|(t,i,v.to_le_bytes())).collect();
  assert_eq!(native,encoded);
  assert_eq!(*a.borrow(),*b.borrow());
  if zero {assert!(original.is_err());assert_eq!(native.len(),4);} else {assert!(original.is_ok());assert_eq!(native.len(),27);}
 }
 #[test] fn success_history_and_trace() {compare(false);}
 #[test] fn rejected_history_and_trace() {compare(true);}
}
