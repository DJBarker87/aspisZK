#![allow(dead_code,unexpected_cfgs)]
#[cfg(kani)] mod proofs {
const CAP:u64=4611686009837453316;
// Cut after the already certified canonical-limb product. No arithmetic stub.
#[kani::proof]
#[kani::unwind(6)]
fn outer_phase_step() {
 let terms:usize=kani::any(); let raw:[u64;4]=kani::any();
 let products:[u64;4]=kani::any();
 kani::assume(terms<22);
 for k in 0..4 {kani::assume(products[k]<=CAP);
   kani::assume(raw[k]<(1u64<<34)+(terms%4) as u64*CAP);}
 let mut updated=raw;
 for k in 0..4 {
   updated[k]+=products[k];
   if terms&3==3 {let limb=&mut updated[k];*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
 }
 let next_terms=terms+1;
 for k in 0..4 {
   // u128 expresses the mathematical invariant when next phase is 3.
   assert!((updated[k] as u128)<(1u128<<34)+(next_terms%4) as u128*CAP as u128);
 }
 assert!(next_terms<=22);
}
#[kani::proof]
fn outer_basis_schedule() {
 let level:usize=kani::any(); kani::assume(level<8);
 let n=1usize<<level;
 let width:usize=kani::any();kani::assume(width<=256 && n<width);
 let j:usize=kani::any();kani::assume(j<n);
 assert!(n+j<256);
 let next=n*2;
 assert!(next==1usize<<(level+1));
 assert!(next<=256);
}
}
