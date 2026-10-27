//! Synthetic kernel experiment. Default execution is refused; dry-run is explicit.
#![allow(unexpected_cfgs)]
use std::{hint::black_box, io::Write, time::{Instant,SystemTime,UNIX_EPOCH}};
use aspis_core::field::{M31,CM31,QM31,P};
pub use aspis_prover::state_only_zerocheck;
mod kernels;
// Source-linked entropy refers to the local hiding module's types.
pub(crate) use kernels::state_only_hiding;
const CONTROLS: &[&str] = &["mask-m31-fixed-fixed","mask-m31-random-random","mask-qm31-fixed-fixed","mask-qm31-random-random"];
const FAMILIES: &[&str] = &["mask-m31","mask-qm31","mask-m31-reject","mask-qm31-reject","pole","m31-inv","qm31-inv","compress","seed-field","seed-salt","seed-field-zero","seed-salt-zero"];
#[derive(Clone,Copy)]
struct Prepared { seed:[u8;32], m:M31, q:QM31, limbs:[M31;16] }
struct Rng(u64);
impl Rng {
 fn next(&mut self)->u64 { self.0=self.0.wrapping_add(0x9e3779b97f4a7c15); let mut z=self.0; z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9); z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb); z^(z>>31) }
 fn seed(&mut self)->[u8;32] { let mut b=[0;32]; for s in b.chunks_exact_mut(8) {s.copy_from_slice(&self.next().to_le_bytes());} b }
 fn m(&mut self)->M31 { M31((self.next() % (P as u64-1)+1) as u32) }
 fn q(&mut self)->QM31 { QM31{c0:CM31::new(self.m(),self.m()),c1:CM31::new(self.m(),self.m())} }
}
#[cfg(target_arch="x86_64")]
#[inline(always)] fn stamp()->(u64,u32) { unsafe { use std::arch::x86_64::*; std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst); _mm_lfence(); let mut aux=0; let t=__rdtscp(&mut aux); _mm_lfence(); std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst); (t,aux) } }
#[inline(never)] fn inverse_m(x:M31)->M31 {x.inv()}
#[inline(never)] fn inverse_q(x:QM31)->QM31 {x.inv()}
trait Outcome {fn outcome(&self)->bool;}
impl<T,E> Outcome for Result<T,E> {fn outcome(&self)->bool {self.is_ok()}}
impl Outcome for bool {fn outcome(&self)->bool {*self}}
impl Outcome for M31 {fn outcome(&self)->bool {true}}
impl Outcome for QM31 {fn outcome(&self)->bool {true}}
fn epoch()->u64 {SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs()}
fn window()->u64 { let v:serde_json::Value=serde_json::from_slice(&std::fs::read("/home/dombarker/project-offloads/QUIET_WINDOW.json").expect("lead's window marker required")).unwrap(); let until=v["until"].as_f64().expect("numeric until").floor() as u64; assert!(epoch()<until,"window expired"); until }
fn main() {
 let a:Vec<_>=std::env::args().collect();
 assert!(a.len()==3 && ["--dry-run","--measure"].contains(&a[1].as_str()),"usage: pv-dudect --dry-run 1000 | --measure 1000000");
 let dry=a[1]=="--dry-run"; let n:usize=a[2].parse().unwrap(); assert!(if dry {n==1000} else {n==1_000_000});
 let deadline=if dry {assert!(!std::path::Path::new("/home/dombarker/project-offloads/QUIET_WINDOW.json").exists(),"dry run must be outside any window");u64::MAX} else {window()};
 let mut rng=Rng(0x563337342d763200); let all=Instant::now();
 for family in CONTROLS.iter().chain(FAMILIES.iter()) {
  let start=Instant::now(); let mut sum=[0u128;2]; let mut count=[0usize;2]; let mut migrations=[0usize;2]; let mut outcomes=[[0usize;2];2];
  let mut out=if dry {None} else {Some(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(format!("{family}.csv")).unwrap()))};
  if let Some(w)=out.as_mut() {writeln!(w,"class,cycles,start_aux,end_aux,valid,outcome").unwrap();}
  // Exactly balanced shuffled class schedule, constructed outside intervals.
  let mut order:Vec<usize>=(0..2*n).map(|i|i&1).collect();
  for i in (1..order.len()).rev() {let j=(rng.next()%(i as u64+1)) as usize;order.swap(i,j);}
  let warm_count=if dry {0} else {10000};
  let mut warm:Vec<usize>=(0..warm_count).map(|i|i&1).collect();
  for i in (1..warm.len()).rev() {let j=(rng.next()%(i as u64+1)) as usize;warm.swap(i,j);}
  warm.extend(order); order=warm;
  // Pregenerate every record through the same random path for both classes.
  // Constant replacement is also outside the sampling loop, as in D297.
  let inputs:Vec<Prepared>=order.iter().map(|&class| {
   let mut p=Prepared {seed:rng.seed(),m:rng.m(),q:rng.q(),limbs:std::array::from_fn(|_|rng.m())};
   if family.ends_with("-fixed-fixed") {p.seed=if class==0 {[0x35;32]} else {[0xa7;32]};}
   else if !family.ends_with("-random-random") && class==0 {
    p.seed=if family.ends_with("-zero") {[0;32]} else {[0x35;32]};
    p.m=M31(7);p.q=QM31::from_cm31(CM31::from_m31(M31(7)));p.limbs=[M31(7);16];
   }
   p
  }).collect();
  let mut prepared_count=[0usize;2];
  for (i,(&class,source)) in order.iter().zip(&inputs).enumerate() {
   let warming=i<warm_count;
   if i%1024==0 {assert!(epoch()<deadline,"window expired");}
   // Common fresh stack lifetime/copy site for every experiment and both classes.
   let mut seed=[0u8;32];seed.copy_from_slice(black_box(&source.seed));
   let fresh=black_box(*source);let m=black_box(fresh.m);let q=black_box(fresh.q);
   let mut limbs=[M31(0);16];limbs.copy_from_slice(black_box(&fresh.limbs));
   let mut exp=kernels::prepare(black_box(seed),if family.ends_with("-reject") {if class==0 {1} else {2}} else {0});
   let values:Vec<_>=if *family=="pole" {(0..1024).map(|_|[[q;2];2]).collect()} else {Vec::new()};
   if !warming {prepared_count[class]+=1;}
   let masks=[u16::MAX;64]; let chi=QM31::ONE; let lambda=QM31{c0:CM31::new(M31(3),M31(5)),c1:CM31::new(M31(7),M31(11))};
   // Dispatch is public and occurs before the first counter read in each arm.
   macro_rules! timed {($e:expr)=>{{if warming {black_box($e);(0,0,0,true)} else {let (t,c)=stamp(); let result=black_box($e); let (u,d)=stamp();(u.wrapping_sub(t),c,d,result.outcome())}}}}
   let (cycles,c,d,outcome)=match *family {
    "mask-m31"|"mask-m31-reject"|"mask-m31-fixed-fixed"|"mask-m31-random-random"=>timed!(kernels::measure_m31(black_box(&mut exp))),
    "mask-qm31"|"mask-qm31-reject"|"mask-qm31-fixed-fixed"|"mask-qm31-random-random"=>timed!(kernels::measure_qm31(black_box(&mut exp))),
    "pole"=>timed!(kernels::ct_pole::all_slots_clear(black_box(&values),black_box(&masks),black_box(chi))),
    "m31-inv"=>timed!(inverse_m(black_box(m))),
    "qm31-inv"=>timed!(inverse_q(black_box(q))),
    "compress"=>timed!(kernels::prover_shared::compress_tagged_tuple(black_box(M31(73)),black_box(&limbs),black_box(lambda))),
    _=>timed!(kernels::seed_check(black_box(&seed))),
   };
   if warming {continue;}
   outcomes[class][outcome as usize]+=1;
   let valid=c==d; if !valid {migrations[class]+=1;} else {sum[class]+=cycles as u128;count[class]+=1;}
   if let Some(w)=out.as_mut(){writeln!(w,"{class},{cycles},{c},{d},{valid},{outcome}").unwrap();}
  }
  if let Some(w)=out.as_mut(){w.flush().unwrap();}
  println!("{}",serde_json::json!({"family":family,"label":if dry {"not a measurement"} else {"kernel timing samples"},"per_class":n,"preparation":"pregenerated records; common fresh buffers","fresh_prepared_per_class":prepared_count,"sanity_control":CONTROLS.contains(family),"valid":count,"migrations":migrations,"outcomes_false_true":outcomes,"mean_cycles":[sum[0] as f64/count[0] as f64,sum[1] as f64/count[1] as f64],"wall_seconds":start.elapsed().as_secs_f64()}));
  if family.starts_with("mask-") {assert!(outcomes[0][0]==0 && outcomes[1][0]==0,"sampler error: abort, retain rows");}
  assert!(migrations==[0,0],"migration detected: abort, retain raw rows");
 }
 eprintln!("total wall seconds: {}",all.elapsed().as_secs_f64());
}
