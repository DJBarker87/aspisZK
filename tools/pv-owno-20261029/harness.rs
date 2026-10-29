use aspis_core::field::{CM31,M31,QM31,P};
use aspis_statement::logup::{build_copy_logup_helper,CopyLogUpRow,LogUpError,LogUpSide};
fn canon(q:QM31)->bool { [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0].into_iter().all(|x|x<P) }
fn raw(x:[u32;4])->QM31 { QM31 { c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3])) } }
fn next(s:&mut u64)->u32 { *s=s.wrapping_mul(6364136223846793005).wrapping_add(1);(*s>>32)as u32 }
// Forward interpreter of HelperArrays.view and HelperPush.run. Retains the
// first error's row and side, unlike the prior Option-only differential.
fn reference(rows:&[CopyLogUpRow],chi:QM31)->Result<Vec<QM31>,LogUpError> {
 let mut out=Vec::with_capacity(rows.len());
 for (index,row) in rows.iter().enumerate() {
  let mut value=QM31::ZERO;
  for producer in [true,false] {
   let (values,weights)=if producer {(row.producer_values,row.producer_weights)}else{(row.consumer_values,row.consumer_weights)};
   for (v,w) in values.into_iter().zip(weights) {
    if w.0!=0 {
     let inverse=chi.sub(v).try_inv().ok_or(LogUpError::ActivePole{row:index,side:if producer{LogUpSide::Producer}else{LogUpSide::Consumer}})?;
     let term=inverse.mul_m31(w);
     value=if producer{value.add(term)}else{value.sub(term)};
    }
   }
  }
  out.push(value);
 } Ok(out)
}
fn main(){
 let chi=raw([7,2,3,4]);let mut seed=992u64;let mut success=0;let mut failure=0;
 for case in 0..512 {
  let rows:Vec<_>=(0..case%19).map(|_|CopyLogUpRow{
   producer_values:std::array::from_fn(|_|raw(std::array::from_fn(|_|next(&mut seed)))),
   consumer_values:std::array::from_fn(|_|raw(std::array::from_fn(|_|next(&mut seed)))),
   producer_weights:std::array::from_fn(|_|M31(next(&mut seed))),
   consumer_weights:std::array::from_fn(|_|M31(next(&mut seed)))}).collect();
  let got=build_copy_logup_helper(&rows,chi);assert_eq!(got,reference(&rows,chi));
  if let Ok(v)=got {assert_eq!(v.len(),rows.len());assert!(v.into_iter().all(canon));success+=1;}else{failure+=1;}
 }
 // Every slot at every row, also with a later competing pole. This checks
 // first-stop order and initialized-prefix traversal without erasing tags.
 let empty=CopyLogUpRow{producer_values:[QM31::ZERO;2],consumer_values:[QM31::ZERO;2],producer_weights:[M31::ZERO;2],consumer_weights:[M31::ZERO;2]};
 for at in 0..17 {for slot in 0..4 {
  let mut rows=vec![empty;19];
  if slot<2 {rows[at].producer_values[slot]=chi;rows[at].producer_weights[slot]=M31::ONE;}
  else {rows[at].consumer_values[slot-2]=chi;rows[at].consumer_weights[slot-2]=M31::ONE;}
  rows[18].producer_values[0]=chi;rows[18].producer_weights[0]=M31::ONE;
  let expected=LogUpError::ActivePole{row:at,side:if slot<2{LogUpSide::Producer}else{LogUpSide::Consumer}};
  assert_eq!(build_copy_logup_helper(&rows,chi),Err(expected));
  assert_eq!(build_copy_logup_helper(&rows,chi),reference(&rows,chi));failure+=1;
 }}
 println!("full Result helper differentials: raw cases=512; successes={success}; errors={failure}; exact row/side first-pole cases=68");
}
