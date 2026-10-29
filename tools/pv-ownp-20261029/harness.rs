use aspis_core::field::{CM31,M31,QM31,P};
use aspis_core::r0_transcript::qm31_sample;
use aspis_core::state_only_prefix::r0::{self as wire,SemanticTranscript,Error};
use aspis_prover::state_only_hiding::r0::prove_sumcheck;
fn raw(x:[u32;4])->QM31 { QM31 {c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3]))} }
fn canon(q:QM31)->bool {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0].into_iter().all(|x|x<P)}
fn next(s:&mut u64)->u32 {*s=s.wrapping_mul(6364136223846793005).wrapping_add(1);(*s>>32)as u32}
// Independent high-word-first u128 division of the unreduced input rank.
// Four remainders already compute rank mod P^4; later four passes are kept.
fn sample_reference(block:&[u8;32])->QM31 {
 let mut rank:[u32;8]=std::array::from_fn(|i|u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()));
 let digits:[u32;8]=std::array::from_fn(|_|{
  let mut remainder=0u128;
  for i in (0..8).rev() {let n=remainder*(1u128<<32)+u128::from(rank[i]);rank[i]=(n/u128::from(P))as u32;remainder=n%u128::from(P);}
  remainder as u32
 });
 raw(digits[..4].try_into().unwrap())
}
// Deterministic test hash; no cryptographic assertion is made about it.
fn hash(parts:&[&[u8]])->[u8;32] {
 let mut s=0x91babcdu64;
 for p in parts {for b in *p {s=s.rotate_left(7)^u64::from(*b);s=s.wrapping_mul(0x9e3779b185ebca87);}}
 std::array::from_fn(|_|next(&mut s)as u8)
}
fn start(seed:u8)->SemanticTranscript {
 let mut t=SemanticTranscript::new(hash,&[seed;48],&[seed.wrapping_add(1);32]).unwrap();
 for row in 0..15 {let payload=vec![0;wire::row_shape(row).unwrap().1];let f=wire::record(row,&payload).unwrap();assert!(canon(t.semantic(row,&f).unwrap()));}
 t
}
fn point_checks(seed:u8,stop:Option<usize>)->usize {
 let mut actual=start(seed);let mut reference=start(seed);let mut alpha=[QM31::ZERO;10];let mut frames=Vec::new();
 for round in 0..10 {let f=wire::record(15+round as u8,&vec![0;28*32]).unwrap();alpha[round]=reference.semantic(15+round as u8,&f).unwrap();frames.extend_from_slice(&f);}
 let mut queries=Vec::new();
 for round in 0..10 {for sample in 0..28 {for assignment in 0..1usize<<(9-round) {
  let p=std::array::from_fn(|i|if i<round {alpha[i]}else if i==round {raw([sample,0,0,0])}else if (assignment>>(9-i))&1==0 {QM31::ZERO}else {QM31::ONE});
  queries.push(p);
 }}}
 queries.push(alpha);let mut at=0;let mut output=Vec::new();
 let got=prove_sumcheck(&mut actual,&mut output,QM31::ZERO,|point|{
  assert_eq!(*point,queries[at],"seed={seed} query={at}");assert!(point.iter().copied().all(canon));
  let reject=stop==Some(at);at+=1;if reject {Err(Error::Public)}else {Ok(QM31::ZERO)}
 });
 if let Some(n)=stop {assert_eq!(got,Err(Error::Public));assert_eq!(at,n+1);}else {assert_eq!(got,Ok((alpha,QM31::ZERO)));assert_eq!(at,28645);assert_eq!(output,frames);assert_eq!(actual.state(),reference.state());}
 at
}
fn main(){
 let mut seed=704u64;let mut samples=0;
 for case in 0..2306 {let block=if case==0 {[0;32]}else if case==1 {[255;32]}else if case<258 {let mut b=[0;32];b[(case-2)/8]=1<<((case-2)%8);b}else {std::array::from_fn(|_|next(&mut seed)as u8)};
  let got=qm31_sample(&block);assert_eq!(got,sample_reference(&block));assert!(canon(got));samples+=1;
 }
 let mut observations=0;
 for seed in [0,1,129,255] {observations+=point_checks(seed,None);}
 for stop in [0,1,511,512,14335,28643,28644] {observations+=point_checks(9,Some(stop));}
 println!("sampler exact-value/canonical comparisons={samples}; complete point schedules=4; query count each=28645; error first-stop schedules=7; observed points={observations}; terminal callback included");
}
