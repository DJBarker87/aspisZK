use aspis_core::field::{CM31,M31,QM31,P};
use aspis_statement::logup::{build_copy_logup_helper,CopyLogUpRow};
fn canon(q:QM31)->bool { [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0].into_iter().all(|x|x<P) }
fn raw(x:[u32;4])->QM31 { QM31 { c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3])) } }
fn next(s:&mut u64)->u32 { *s=s.wrapping_mul(6364136223846793005).wrapping_add(1);(*s>>32)as u32 }
fn reference(rows:&[CopyLogUpRow],chi:QM31)->Option<Vec<QM31>> {
 let mut out=Vec::new();
 for row in rows {
  let mut value=QM31::ZERO;
  for i in 0..2 {if row.producer_weights[i]!=M31::ZERO {
   let inv=chi.sub(row.producer_values[i]).try_inv()?;
   let t=inv.mul_m31(row.producer_weights[i]);value=value.add(t);
  }}
  for i in 0..2 {if row.consumer_weights[i]!=M31::ZERO {
   let inv=chi.sub(row.consumer_values[i]).try_inv()?;
   let t=inv.mul_m31(row.consumer_weights[i]);value=value.sub(t);
  }}
  out.push(value);
 } Some(out)
}
fn main(){
 let mut seed=992u64;let mut scale_count=0;let mut accepted=0;let mut poles=0;
 for n in 0..4096 {
  let a=raw(std::array::from_fn(|_|next(&mut seed)));
  let w=M31(if n<4 {[0,1,P,u32::MAX][n]}else{next(&mut seed)});
  let got=a.mul_m31(w);
  let expected=raw([a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0].map(|x|((u64::from(x)*u64::from(w.0))%u64::from(P))as u32));
  assert_eq!(got,expected);assert!(canon(got));scale_count+=1;
  let mut bytes=[0u8;16];a.write_le_bytes(&mut bytes);
  assert_eq!(QM31::from_le_bytes(&bytes).is_some(),canon(a));
 }
 for case in 0..128 {
  let chi=raw([7,2,3,4]);
  let rows:Vec<_>=(0..(case%17)).map(|r| {
   let mut mk=||raw(std::array::from_fn(|_|next(&mut seed)%P));
   let mut row=CopyLogUpRow {producer_values:[mk(),mk()],consumer_values:[mk(),mk()],producer_weights:[M31::ONE,M31(2)],consumer_weights:[M31(3),M31::ZERO]};
   if case%11==0 && r==0 {row.producer_values[0]=chi;}
   row
  }).collect();
  let actual=build_copy_logup_helper(&rows,chi);let expected=reference(&rows,chi);
  assert_eq!(actual.as_ref().ok(),expected.as_ref());
  if let Ok(out)=actual {assert_eq!(out.len(),rows.len());assert!(out.into_iter().all(canon));accepted+=1;}else{poles+=1;}
 }
 // Actual core sampler, whose reduce_rank may be arbitrary for this invariant.
 for _ in 0..4096 {let b:[u8;32]=std::array::from_fn(|_|next(&mut seed)as u8);assert!(canon(aspis_core::r0_transcript::qm31_sample(&b)));}
 println!("scale differential={scale_count}; helper accepted={accepted}; poles={poles}; actual core sampler canonical=4096; byte roundtrip acceptance=4096");
}
