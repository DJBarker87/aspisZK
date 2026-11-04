use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct NGQ_Oracle<'a> { log: &'a Cell<(usize,u8,u8,u8,u8)>, replies: &'a [[u8;32];2], window: usize }
impl aspis_core::Digest32 for NGQ_Oracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),32);assert_eq!(parts[1].len(),1);
  let (n,s0,t0,s1,t1)=self.log.get(); assert!(n<2);
  if n==0 {self.log.set((1,parts[0][self.window],parts[1][0],s1,t1));}
  else {self.log.set((2,s0,t0,parts[0][self.window],parts[1][0]));}
  self.replies[n]
 }
}
impl<H:aspis_core::Digest32> Transcript<H> {
fn NGQ_pair0(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[0]=self.hash.digest(&[&state,&[1]]);
        advances[0]=self.hash.digest(&[&state,&[2]]);state=advances[0];
(blocks,advances,state)
}
fn NGQ_pair1(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[1]=self.hash.digest(&[&state,&[1]]);
        advances[1]=self.hash.digest(&[&state,&[2]]);state=advances[1];
(blocks,advances,state)
}
fn NGQ_pair2(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[2]=self.hash.digest(&[&state,&[1]]);
        advances[2]=self.hash.digest(&[&state,&[2]]);state=advances[2];
(blocks,advances,state)
}
fn NGQ_pair3(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[3]=self.hash.digest(&[&state,&[1]]);
        advances[3]=self.hash.digest(&[&state,&[2]]);state=advances[3];
(blocks,advances,state)
}
fn NGQ_pair4(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[4]=self.hash.digest(&[&state,&[1]]);
        advances[4]=self.hash.digest(&[&state,&[2]]);state=advances[4];
(blocks,advances,state)
}
fn NGQ_pair5(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[5]=self.hash.digest(&[&state,&[1]]);
        advances[5]=self.hash.digest(&[&state,&[2]]);state=advances[5];
(blocks,advances,state)
}
fn NGQ_pair6(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[6]=self.hash.digest(&[&state,&[1]]);
        advances[6]=self.hash.digest(&[&state,&[2]]);state=advances[6];
(blocks,advances,state)
}
fn NGQ_pair7(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {
blocks[7]=self.hash.digest(&[&state,&[1]]);
        advances[7]=self.hash.digest(&[&state,&[2]]);state=advances[7];
(blocks,advances,state)
}
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair0() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair0(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==0 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==0 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==0 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==0 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair1() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair1(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==1 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==1 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==1 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==1 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair2() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair2(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==2 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==2 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==2 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==2 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair3() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair3(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==3 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==3 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==3 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==3 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair4() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair4(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==4 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==4 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==4 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==4 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair5() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair5(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==5 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==5 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==5 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==5 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair6() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair6(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==6 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==6 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==6 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==6 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair7() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{log:&log,replies:&replies,window:j};
 let t=Transcript{state,hash};
 let (b,a,final_state)=t.NGQ_pair7(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p==7 {replies[0][j]} else {blocks[p][j]})
  && a[p][j]==(if p==7 {replies[1][j]} else {advances[p][j]})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[p][j]==(if p==7 {replies[0][j]^1} else {blocks[p][j]}) && log.get()==(2,state[j],1,state[j],2) && a[p][j]==(if p==7 {replies[1][j]} else {advances[p][j]}) && final_state[j]==replies[1][j]);
}
