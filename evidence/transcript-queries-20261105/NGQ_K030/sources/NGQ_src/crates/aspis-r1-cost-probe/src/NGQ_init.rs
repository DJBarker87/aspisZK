use super::*;
#[derive(Clone,Copy)] struct NGQ_NoHash;
impl aspis_core::Digest32 for NGQ_NoHash {
 fn digest(&self,_:&[&[u8]])->[u8;32] {panic!("unexpected digest in initialization")}
}
impl<H:aspis_core::Digest32> Transcript<H> {
 fn NGQ_init(&self)->([[u8;32];8],[[u8;32];8],[u8;32]) {
  let mut blocks=[[0;32];8];let mut advances=blocks; let mut state=self.state;
  (blocks,advances,state)
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_init() {
 let state:[u8;32]=kani::any();let t=Transcript{state,hash:NGQ_NoHash};
 let p:usize=kani::any();let j:usize=kani::any();kani::assume(p<8 && j<32);
 let (b,a,s)=t.NGQ_init();let correct=b[p][j]==0 && a[p][j]==0 && s[j]==state[j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[0][0]==1);
}
