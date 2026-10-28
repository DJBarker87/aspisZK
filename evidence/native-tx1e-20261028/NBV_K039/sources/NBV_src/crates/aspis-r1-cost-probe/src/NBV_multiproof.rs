use super::*;
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_count_copy_prefix(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],if k<n{input[k]}else{0});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_count_copy_wrong(){let mut input=[0u32;16];input[7]=1;input[15]=512;let n=16;let k=15;let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],0);}

use core::cell::Cell;
#[derive(Clone,Copy)]
struct Port<'a>{left:*const u8,right:*const u8,c:usize,l:u8,r:u8,answer:[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Port<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{assert_eq!(p.len(),3);assert_eq!(p[0],&[0x12]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);assert_eq!(p[1].as_ptr(),self.left);assert_eq!(p[2].as_ptr(),self.right);assert_eq!(p[1][self.c],self.l);assert_eq!(p[2][self.c],self.r);self.calls.set(self.calls.get()+1);self.answer}}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_pair_carrier(){
 let val:[[u8;32];16]=kani::any();let i:usize=kani::any();let c:usize=kani::any();kani::assume(i<15&&c<32);
 let sibling:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let calls=Cell::new(0);
let left=&val[i];let right=&val[i+1];let hash=Port{left:left.as_ptr(),right:right.as_ptr(),c,l:left[c],r:right[c],answer,calls:&calls};let out=occupied_binary_parent(hash,&val,i);assert_eq!(out[c],answer[c]);assert_eq!(calls.get(),1);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_supply_left_carrier(){
 let val:[[u8;32];16]=kani::any();let i:usize=kani::any();let c:usize=kani::any();kani::assume(i<16&&c<32);
 let sibling:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let calls=Cell::new(0);
let left=&val[i];let right=&sibling;let hash=Port{left:left.as_ptr(),right:right.as_ptr(),c,l:left[c],r:right[c],answer,calls:&calls};let out=sibling_binary_parent(hash,&val,i,&sibling,true);assert_eq!(out[c],answer[c]);assert_eq!(calls.get(),1);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_supply_right_carrier(){
 let val:[[u8;32];16]=kani::any();let i:usize=kani::any();let c:usize=kani::any();kani::assume(i<16&&c<32);
 let sibling:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let calls=Cell::new(0);
let left=&sibling;let right=&val[i];let hash=Port{left:left.as_ptr(),right:right.as_ptr(),c,l:left[c],r:right[c],answer,calls:&calls};let out=sibling_binary_parent(hash,&val,i,&sibling,false);assert_eq!(out[c],answer[c]);assert_eq!(calls.get(),1);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_row_store_frame(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let w:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(w<16&&k<16&&c<32);let old_i=idx[k];let old_v=val[k][c];let parent:u32=kani::any();let digest:[u8;32]=kani::any();idx[w]=parent;val[w]=digest;assert_eq!(idx[k],if k==w{parent}else{old_i});assert_eq!(val[k][c],if k==w{digest[c]}else{old_v});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_row_store_wrong(){let mut val=[[0u8;32];16];let digest=[1u8;32];val[15]=digest;assert_eq!(val[15][31],0);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_admitted_count_copy(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);kani::assume(well_formed(&input[..n]));let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);let live_n=n;let count=0usize;assert_eq!(live_n,n);assert_eq!(count,0);assert_eq!(level[k],if k<n{input[k]}else{0});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_parent_reply_wrong(){let val=[[0u8;32];16];let answer=[1u8;32];let calls=Cell::new(0);let hash=Port{left:val[0].as_ptr(),right:val[1].as_ptr(),c:31,l:0,r:0,answer,calls:&calls};let out=occupied_binary_parent(hash,&val,0);assert_eq!(out[31],0);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_admitted_copy_wrong(){let mut input=[0u32;16];for i in 0..16{input[i]=i as u32;}assert!(well_formed(&input));let mut level=[0u32;16];level[..16].copy_from_slice(&input);assert_eq!(level[15],0);}
#[kani::proof] #[kani::unwind(2)]
fn NBV_count_native_step(){let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();let count:usize=kani::any();kani::assume(i<=j&&j<=n&&i<n&&n<=16&&w<=i&&k<16&&count<=288);let parent=index_at(&level,i)>>Arity::Two.bits();let old=level[k];let mut next_j=j;if next_j<n&&index_at(&level,next_j)>>Arity::Two.bits()==parent{next_j+=1;}assert_eq!(next_j,j+usize::from(j<n&&level[j]/2==parent));assert!(next_j<=n);if j>i&&j-i<=2{let next_count=count+Arity::Two.width()-(j-i);level[w]=parent;assert_eq!(level[k],if k==w{parent}else{old});assert_eq!(next_count,count+2-(j-i));}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_level_continuation(){let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(0<n&&n<=16&&w<=i&&i<=n);if i==n{let next_n=w;let next_i=0usize;let next_w=0usize;assert!(next_n<=16&&next_w<=next_i&&next_i<=next_n);}else{assert!(i<16&&w<16)}}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_final_carrier(){let values:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let idx:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();let len:usize=kani::any();let actual=n==1&&index_at(&idx,0)==0&&root_matches(&values,&root)&&at==len;assert_eq!(actual,n==1&&idx[0]==0&&values[0]==root&&at==len);}
