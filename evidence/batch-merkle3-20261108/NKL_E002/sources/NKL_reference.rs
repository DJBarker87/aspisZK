#![no_std]
#[derive(Clone,Copy)]
pub enum Error { Parse, Merkle }
#[derive(Clone,Copy)]
pub struct State { pub idx:[u32;16], pub val:[[u8;32];16], pub d:usize, pub error:Option<Error> }
pub trait Children:Copy {
 fn keys(self,queries:[u32;22],lo:usize,n:usize,tree:usize)->[u64;16];
 fn leaf(self,tree:usize,q:&[u8])->[u8;32];
 fn count(self,idx:[u32;16],d:usize)->Option<usize>;
 fn verify(self,root:[u8;32],state:State,nodes:&[u8])->(bool,State);
}
pub fn leaf_step(mut state:State,index:u32,leaf:[u8;32])->State {
 if state.d>0 && state.idx[state.d-1]==index {
  if state.val[state.d-1]!=leaf { state.error=Some(Error::Merkle); }
 } else {
  state.idx[state.d]=index; state.val[state.d]=leaf; state.d+=1;
 }
 state
}
pub fn padding_word(bytes:&[u8],at:usize)->bool {
 bytes[at]!=0 || bytes[at+1]!=0 || bytes[at+2]!=0 || bytes[at+3]!=0 || bytes[at+4]!=0 || bytes[at+5]!=0 || bytes[at+6]!=0 || bytes[at+7]!=0
}
pub fn padding(bytes:&[u8],start:usize)->bool {
 let mut at=start; let mut bad=false;
 while at+8<=bytes.len() && !bad { bad=padding_word(bytes,at); at+=8; }
 bad
}
pub fn tail<C:Children>(children:C,root:[u8;32],state:State,nodes:&[u8],capacity:usize)->(Result<(),Error>,State) {
 match children.count(state.idx,state.d) {
  None=>(Err(Error::Merkle),state),
  Some(count)=>{
   if count>capacity || padding(nodes,32*count) { (Err(Error::Parse),state) }
   else {
    let (valid,after)=children.verify(root,state,&nodes[..32*count]);
    if valid { (Ok(()),after) } else { (Err(Error::Merkle),after) }
   }
  }
 }
}
pub fn slot_start(s:usize)->usize {
 let sizes=[146usize,146,128,172,172,150]; let mut at=28359; let mut i=0;
 while i<s {at+=32*sizes[i];i+=1;} at
}
pub fn batch_tree<C:Children>(children:C,proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,idx:[u32;16],val:[[u8;32];16])->(Result<(),Error>,State) {
 let (lo,n)=if batch==0{(0,10)}else{(10,12)};
 let keys=children.keys(queries,lo,n,tree); let state=State{idx,val,d:0,error:None};
 let state=leaf_at(children,proof,keys,lo,n,tree,state,0);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,1);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,2);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,3);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,4);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,5);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,6);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,7);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,8);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,9);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,10);
 let state=leaf_at(children,proof,keys,lo,n,tree,state,11);

 match state.error {
  Some(e)=>(Err(e),state),
  None=>{let s=3*batch+tree;let sizes=[146usize,146,128,172,172,150];tail(children,root,state,&proof[slot_start(s)..slot_start(s+1)],sizes[s])}
 }
}

pub fn leaf_at<C:Children>(children:C,proof:&[u8],keys:[u64;16],lo:usize,n:usize,tree:usize,state:State,pos:usize)->State {
 if pos<n && state.error.is_none() {
  let key=keys[pos];let index=(key>>8)as u32;let ordinal=lo+(key&255)as usize;
  let at=10055+ordinal*832;let leaf=children.leaf(tree,&proof[at..at+832]);leaf_step(state,index,leaf)
 } else { state }
}
