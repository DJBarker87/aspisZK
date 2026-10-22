//! Measurement differential corpus; fixture probes, not a universal proof.
use aspis_core::r0::CodeField;
use sha2::{Digest,Sha256};
use aspis_core::field::{M31,CM31,QM31,WideExact};
use aspis_z4b_probe::{R1PublicChallenges,p_r1_check};
use std::{fs,time::Instant};
use serde_json::json;
struct Rng(u64);
impl Rng {
 fn word(&mut self)->u32 { self.0^=self.0<<13;self.0^=self.0>>7;self.0^=self.0<<17;(self.0%0x7fff_ffff)as u32 }
 fn w(&mut self)->WideExact { WideExact::new(self.q(),self.q()) }
 fn q(&mut self)->QM31 { QM31{c0:CM31::new(M31(self.word()),M31(self.word())),c1:CM31::new(M31(self.word()),M31(self.word()))} }
}
fn main(){
 assert!(!cfg!(debug_assertions));
 let out=std::env::args().nth(1).unwrap();let mut rng=Rng(0x525f315f20261022);let mut rows=vec![];
 // Four independent full canonical cases; remaining cases deliberately exercise
 // early rejection, HalfOK and degenerate/rank paths at randomized challenges.
 for i in 0..1000 {
  let mut ch=R1PublicChallenges{alpha:std::array::from_fn(|_|rng.q()),z:std::array::from_fn(|_|std::array::from_fn(|_|rng.q())),gamma:rng.w(),kappa:rng.w(),alpha0:rng.w(),alpha1:rng.w(),queries:vec![]};
  while ch.queries.len()<22 {let q=rng.word()%(1<<18);if !ch.queries.contains(&q){ch.queries.push(q);}}
  let case=if i<4 {"full-canonical"} else {match i%4 {
   0=>{ch.queries.push(ch.queries[0]);"duplicate-query"},
   1=>{ch.queries[0]=(1<<18)+rng.word();"out-of-range-query"},
   2=>{ch.alpha[9]=QM31::from_m31(M31(2).inv());"HalfOK"},
   _=>{ch.alpha=[QM31::ZERO;10];"degenerate-rank"},
  }};
  let mut digest=Sha256::new();
  for v in ch.alpha.iter().chain(ch.z.iter().flatten()) {
   for x in [v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0] {digest.update(x.to_le_bytes());}
  }
  for v in [ch.gamma,ch.kappa,ch.alpha0,ch.alpha1] {for x in v.to_limbs(){digest.update(x.to_le_bytes());}}
  for q in &ch.queries {digest.update(q.to_le_bytes());}
  let input_sha256=format!("{:x}",digest.finalize());
  let now=Instant::now();let (accepted,_)=p_r1_check(&ch);
  rows.push(json!({"id":i,"case":case,"input_sha256":input_sha256,"accepted":accepted,"seconds":now.elapsed().as_secs_f64()}));
  fs::write(&out,serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
  eprintln!("DIFF {i} {case} {accepted}");
 }
}
