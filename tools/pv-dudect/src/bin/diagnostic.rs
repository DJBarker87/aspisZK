//! diagnostic, not a V374 measurement. No quiet window permitted.
use std::{hint::black_box,io::Write};
use aspis_core::field::{M31,CM31,QM31,P};
pub use aspis_prover::state_only_zerocheck;
#[path="../kernels.rs"] mod kernels;
pub(crate) use kernels::state_only_hiding;
struct Rng(u64);
impl Rng {
 fn next(&mut self)->u64 { self.0=self.0.wrapping_add(0x9e3779b97f4a7c15); let mut z=self.0; z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9); z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb); z^(z>>31) }
 fn seed(&mut self)->[u8;32] { let mut b=[0;32]; for s in b.chunks_exact_mut(8) {s.copy_from_slice(&self.next().to_le_bytes());} b }
 fn m(&mut self)->M31 { M31((self.next() % (P as u64-1)+1) as u32) }
 fn q(&mut self)->QM31 { QM31{c0:CM31::new(self.m(),self.m()),c1:CM31::new(self.m(),self.m())} }
}
#[cfg(target_arch="x86_64")]
#[inline(always)] fn stamp()->(u64,u32) { unsafe { use std::arch::x86_64::*; std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst); _mm_lfence(); let mut aux=0; let t=__rdtscp(&mut aux); _mm_lfence(); std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst); (t,aux) } }

fn main() {
 assert!(!std::path::Path::new("/home/dombarker/project-offloads/QUIET_WINDOW.json").exists());
 let n=1_000_000usize;
 let names=["mask-m31-fixed-fixed","mask-m31-random-random","mask-m31-fixed-random-fresh","mask-qm31-fixed-fixed","mask-qm31-random-random","mask-qm31-fixed-random-fresh"];
 let mut rng=Rng(0x563337342d763200);
 // Twelve equally populated cells in one shuffled schedule, not sequential tests.
 let mut order:Vec<usize>=(0..12*n).map(|i|i%12).collect();
 for i in (1..order.len()).rev(){let j=(rng.next()%(i as u64+1)) as usize;order.swap(i,j);}
 // Every cell draws by the identical generator path, then fixed cells are replaced.
 // One contiguous backing allocation, identical stride and copy path for all cells.
 let seeds:Vec<[u8;32]>=order.iter().map(|&cell|{
  let mut s=rng.seed();let pair=cell/2;let class=cell%2;
  if pair%3==0 {s=if class==0 {[0x35;32]}else{[0xa7;32]};}
  if pair%3==2 && class==0 {s=[0x35;32];} s
 }).collect();
 let mut files:Vec<_>=names.iter().map(|name|{let mut f=std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(format!("{name}.csv")).unwrap());writeln!(f,"class,cycles,start_aux,end_aux,valid,outcome").unwrap();f}).collect();
 // Untimed balanced warmup uses the same setup/call paths.
 for i in 0..10000 {let mut exp=kernels::prepare(black_box(seeds[i]),0);if order[i]/2<3 {black_box(kernels::measure_m31(&mut exp)).unwrap();}else{black_box(kernels::measure_qm31(&mut exp)).unwrap();}}
 for (&cell,source) in order.iter().zip(&seeds) {
  // A fresh lifetime in the same stack slot; no fixed-class retained buffer.
  let mut fresh=[0u8;32];fresh.copy_from_slice(black_box(source));
  let mut exp=kernels::prepare(black_box(fresh),0);
  let pair=cell/2;let class=cell%2;
  let (cycles,c,d,ok)=if pair<3 {let(t,c)=stamp();let r=black_box(kernels::measure_m31(black_box(&mut exp)));let(u,d)=stamp();(u-t,c,d,r.is_ok())}else{let(t,c)=stamp();let r=black_box(kernels::measure_qm31(black_box(&mut exp)));let(u,d)=stamp();(u-t,c,d,r.is_ok())};
  writeln!(files[pair],"{class},{cycles},{c},{d},{},{}",c==d,ok).unwrap();
 }
 for f in &mut files {f.flush().unwrap();}
 println!("diagnostic, not a V374 measurement; six interleaved pairs, 1000000/class each");
}
