use std::cell::RefCell;
mod multiproof {
 pub const LEAF_BITS:u32=17;
 pub fn binary_parent(prog:super::ProgramOne,left:&[u8;32],right:&[u8;32]) {
  *prog.table.borrow_mut()=Some((prog.answer,*left,*right));
 }
}
type Table=RefCell<Option<([u8;32],[u8;32],[u8;32])>>;
struct ProgramOne<'a> {table:&'a Table,answer:[u8;32]}
struct Level {p:usize,vals:[Option<[u8;32]>;2]}
impl Level {fn get(&self,i:&usize)->Option<&[u8;32]> {if *i==2*self.p {self.vals[0].as_ref()} else if *i==2*self.p+1 {self.vals[1].as_ref()} else {None}}}
struct Coins {draws:[[u8;32];3],next:usize}
impl Coins {fn coin(&mut self)->[u8;32] {let v=self.draws[self.next];self.next+=1;v}}
#[derive(Default)] struct Next {entry:Option<(usize,[u8;32])>}
impl Next {fn insert(&mut self,p:usize,v:[u8;32]) {self.entry=Some((p,v));}}
#[derive(Default)] struct Kids {entry:Option<(usize,[[u8;32];2])>}
impl Kids {fn insert(&mut self,p:usize,v:[[u8;32];2]) {self.entry=Some((p,v));}}
include!("native.rs");
#[cfg(kani)] #[kani::proof] #[kani::unwind(34)]
fn parent_transition() {
 let p:usize=kani::any();kani::assume(p<65536);
 let depth:u32=kani::any();kani::assume(depth<17);
 let vals:[Option<[u8;32]>;2]=kani::any();
 let draws:[[u8;32];3]=kani::any();let root:[u8;32]=kani::any();
 let reads:usize=kani::any();kani::assume(reads<usize::MAX);
 let mut n=0;
 let left=match vals[0] {Some(v)=>v,None=>{let v=draws[n];n+=1;v}};
 let right=match vals[1] {Some(v)=>v,None=>{let v=draws[n];n+=1;v}};
 let answer=if depth==16 {root} else {let v=draws[n];n+=1;v};
 let level=Level{p,vals};let table=RefCell::new(None);let mut coins=Coins{draws,next:0};
 let mut r=reads;let mut next=Next::default();let mut kids=Kids::default();
 native(&table,&mut coins,&level,root,depth,p,&mut r,&mut next,&mut kids);
 assert_eq!(coins.next,n);assert_eq!(coins.draws,draws);assert_eq!(r,reads+1);
 assert_eq!(next.entry,Some((p,answer)));assert_eq!(kids.entry,Some((p,[left,right])));
 assert_eq!(*table.borrow(),Some((answer,left,right)));
}
