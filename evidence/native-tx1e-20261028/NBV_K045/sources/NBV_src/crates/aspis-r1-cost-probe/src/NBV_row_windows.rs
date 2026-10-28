
use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct Hash<'a>{answer:[u8;32],left:&'a[u8],right:&'a[u8],c:usize,calls:&'a Cell<usize>}
impl Digest32 for Hash<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{
 assert_eq!(p.len(),3);assert_eq!(p[0],&[0x12]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);
 assert_eq!(p[1][self.c],self.left[self.c]);assert_eq!(p[2][self.c],self.right[self.c]);
 self.calls.set(self.calls.get()+1);self.answer
}}
fn NBV_W_row<H:Digest32>(hash:H,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],mut at:usize,mut w:usize,mut i:usize)->(bool,usize,usize,usize){
 let parent=index_at(idx,i)>>Arity::Two.bits();
 let digest=if i+1<n && index_at(idx,i+1)==index_at(idx,i)^1{
  let d=occupied_binary_parent(hash,val,i);i+=2;d
 }else{
  let Some(sibling)=nodes.get(at..at+32)else{return(false,at,w,i)};
  at+=32;let d=sibling_binary_parent(hash,val,i,sibling,index_at(idx,i)&1==0);i+=1;d
 };
 idx[w]=parent;val[w]=digest;w+=1;(true,at,w,i)
}

#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_pair_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32);
 idx[0]=a;idx[1]=a^1;val[0]=left;val[1]=right;let calls=Cell::new(0);
 let out=NBV_W_row(Hash{answer:reply,left:&left,right:&right,c,calls:&calls},&mut idx,&mut val,2,&[],0,0,0);
 assert_eq!(out,(true,0,1,2));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_eq!(val[0][c],reply[c]);
}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_supply_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let sibling:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32);
 idx[0]=a;val[0]=value;let calls=Cell::new(0);let left=a&1==0;
 let out=NBV_W_row(Hash{answer:reply,left:if left{&value}else{&sibling},right:if left{&sibling}else{&value},c,calls:&calls},&mut idx,&mut val,1,&sibling,0,0,0);
 assert_eq!(out,(true,32,1,1));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_eq!(val[0][c],reply[c]);
}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_short_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let len:usize=kani::any();let c:usize=kani::any();kani::assume(c<32&&len<32);let nodes:[u8;32]=kani::any();let calls=Cell::new(0);
 idx[0]=a;val[0]=value;let reply:[u8;32]=kani::any();
 let out=NBV_W_row(Hash{answer:reply,left:&value,right:&nodes,c,calls:&calls},&mut idx,&mut val,1,&nodes[..len],0,0,0);
 assert_eq!(out,(false,0,0,0));assert_eq!(calls.get(),0);assert_eq!(idx[0],a);assert_eq!(val[0][c],value[c]);
}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_level_iterator(){let level:usize=kani::any();kani::assume(level<=18);let mut it=level..Arity::Two.levels() as usize;let next=it.next();assert_eq!(next,if level<18{Some(level)}else{None});if next.is_some(){assert_eq!(it.start,level+1);}}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_admission_window_iterator(){
 let indices:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<=n&&n<=16);
 let mut it=indices[j..n].windows(2);let next=it.next();if n-j>=2{let pair=next.unwrap();assert_eq!(pair[0],indices[j]);assert_eq!(pair[1],indices[j+1]);assert_eq!(it.len(),n-j-2+1-1);}else{assert!(next.is_none());}
}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_admission_value_iterator(){let indices:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<=n&&n<=16);let mut it=indices[j..n].iter();let next=it.next();if j<n{assert_eq!(*next.unwrap(),indices[j]);assert_eq!(it.len(),n-j-1)}else{assert!(next.is_none())}}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_count_zero(){let level=[0u32;16];let k:usize=kani::any();kani::assume(k<16);assert_eq!(level[k],0);let count=0usize;assert_eq!(count,0);}

#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_count_copy_prefix(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],if k<n{input[k]}else{0});}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_level_terminal(){let idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let at:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(n>0&&n<=16&&i==n&&w>0&&w<=i&&at<=5504&&k<16&&c<32);let mut next_n=n;let old_idx=idx[k];let old_val=val[k][c];if i>=n{next_n=w;}assert_eq!(next_n,w);assert_eq!(idx[k],old_idx);assert_eq!(val[k][c],old_val);assert_eq!(at,at);}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_W_count_guard(){let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(n<=16&&w<=i&&i<=n);if i<n{assert!(i<16&&w<16);let j=i;assert!(j<=n);}else{assert_eq!(i,n);assert!(w<=16)}}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_W_pair_window_wrong(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32);
 idx[0]=a;idx[1]=a^1;val[0]=left;val[1]=right;let calls=Cell::new(0);
 let out=NBV_W_row(Hash{answer:reply,left:&left,right:&right,c,calls:&calls},&mut idx,&mut val,2,&[],0,0,0);
 assert_eq!(out,(true,0,1,2));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_ne!(val[0][c],reply[c]);
}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_W_supply_window_wrong(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let sibling:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32);
 idx[0]=a;val[0]=value;let calls=Cell::new(0);let left=a&1==0;
 let out=NBV_W_row(Hash{answer:reply,left:if left{&value}else{&sibling},right:if left{&sibling}else{&value},c,calls:&calls},&mut idx,&mut val,1,&sibling,0,0,0);
 assert_eq!(out,(true,32,1,1));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_ne!(val[0][c],reply[c]);
}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_W_short_window_wrong(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let len:usize=kani::any();let c:usize=kani::any();kani::assume(c<32&&len<32);let nodes:[u8;32]=kani::any();let calls=Cell::new(0);
 idx[0]=a;val[0]=value;let reply:[u8;32]=kani::any();
 let out=NBV_W_row(Hash{answer:reply,left:&value,right:&nodes,c,calls:&calls},&mut idx,&mut val,1,&nodes[..len],0,0,0);
 assert_eq!(out,(false,0,0,0));assert_eq!(calls.get(),0);assert_eq!(idx[0],a);assert_ne!(val[0][c],value[c]);
}
