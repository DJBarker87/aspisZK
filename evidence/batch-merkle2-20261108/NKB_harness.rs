use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NKB_fragments.rs"));
#[derive(Clone,Copy)]
struct NoDigest;
impl Digest32 for NoDigest { fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"no digest after rejected count");[0;32]} }
fn rejected_count(arity:Arity,indices:&[u32])->Option<usize>{assert!(matches!(arity,Arity::Two));assert!(indices.len()<=16);None}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(multiproof::node_count,rejected_count)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn count_reject(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let d:usize=kani::any();kani::assume(d<=16);let root:[u8;32]=kani::any();
 let result=terminal_fragment(&[],root,0,&mut idx,&mut val,d,NoDigest);
 assert!(matches!(result,Err(Error::Merkle)));
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);assert_eq!(idx[j],before_i[j]);
 #[cfg(not(NKB_invert))] assert_eq!(val[j][k],before_v[j][k]);
 #[cfg(NKB_invert)] assert_ne!(val[j][k],before_v[j][k]);
}

#[derive(Clone,Copy)]
struct LeafReply<'a>{proof:&'a[u8],ordinal:usize,tree:usize,byte:usize,reply:[u8;32],calls:&'a core::cell::Cell<usize>}
impl Digest32 for LeafReply<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
 assert_eq!(self.calls.get(),0);self.calls.set(1);assert_eq!(parts.len(),2);
 assert_eq!(parts[0].len(),832);assert_eq!(parts[0].as_ptr(),self.proof.as_ptr().wrapping_add(compact::OFF_OPENINGS+self.ordinal*832));
 assert!(self.byte<832);assert_eq!(parts[0][self.byte],self.proof[compact::OFF_OPENINGS+self.ordinal*832+self.byte]);
 assert_eq!(parts[1],&self.tree.to_le_bytes());self.reply
}}
fn logged_leaf<H:Digest32>(hash:H,tree:usize,q:&[u8])->[u8;32]{hash.digest(&[q,&tree.to_le_bytes()])}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(super::batch_leaf,logged_leaf)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn leaf_step(){
 let proof:[u8;57607]=kani::any();let keys:[u64;16]=kani::any();let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;
 let pos:usize=kani::any();let d:usize=kani::any();let n:usize=kani::any();let batch:usize=kani::any();let tree:usize=kani::any();
 kani::assume(batch<2&&tree<3);let(lo,expected_n)=if batch==0{(0,10)}else{(10,12)};kani::assume(n==expected_n&&pos<n&&d<=pos);
 let key=keys[pos];kani::assume((key&255)<n as u64&&(key>>8)<262144);
 let ordinal=lo+(key&255)as usize;let index=(key>>8)as u32;let reply:[u8;32]=kani::any();let calls=core::cell::Cell::new(0);
 let hash=LeafReply{proof:&proof,ordinal,tree,byte:0,reply,calls:&calls};
 let same=d>0&&before_i[d-1]==index;let consistent=!same||before_v[d-1]==reply;
 let actual=leaf_fragment(&proof,tree,hash,lo,n,keys,&mut idx,&mut val,d,pos);
 assert_eq!(calls.get(),1);
 if !consistent{assert!(matches!(actual,Err(Error::Merkle)))}else{assert_eq!(actual.unwrap(),(if same{d}else{d+1},pos+1))}
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);
 let changed=consistent&&!same&&j==d;assert_eq!(idx[j],if changed{index}else{before_i[j]});
 let expected=if changed{reply[k]}else{before_v[j][k]};
 #[cfg(not(NKB_invert))] assert_eq!(val[j][k],expected);
 #[cfg(NKB_invert)] assert_ne!(val[j][k],expected);
}

#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(super::batch_leaf,logged_leaf)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn prefix_step(){
 let proof:[u8;57607]=kani::any();let keys:[u64;16]=kani::any();let pos:usize=kani::any();let batch:usize=kani::any();let tree:usize=kani::any();
 kani::assume(batch<2&&tree<3);let(lo,n)=if batch==0{(0,10)}else{(10,12)};kani::assume(pos<n);
 let key=keys[pos];kani::assume((key&255)<n as u64&&(key>>8)<262144);let ordinal=lo+(key&255)as usize;
 let reply:[u8;32]=kani::any();let calls=core::cell::Cell::new(0);let byte:usize=kani::any();kani::assume(byte<832);let hash=LeafReply{proof:&proof,ordinal,tree,byte,reply,calls:&calls};
 let(index,leaf,next)=prefix_fragment(&proof,tree,hash,lo,keys,pos);assert_eq!(calls.get(),1);assert_eq!(index,(key>>8)as u32);assert_eq!(next,pos+1);
 let k:usize=kani::any();kani::assume(k<32);
 #[cfg(not(NKB_invert))] assert_eq!(leaf[k],reply[k]);
 #[cfg(NKB_invert)] assert_ne!(leaf[k],reply[k]);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn dedup_step(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let d:usize=kani::any();kani::assume(d<16);
 let index:u32=kani::any();let leaf:[u8;32]=kani::any();let same=d>0&&idx[d-1]==index;let good=!same||val[d-1]==leaf;
 let result=dedup_fragment(&mut idx,&mut val,d,index,leaf);
 if !good {assert!(matches!(result,Err(Error::Merkle)))} else {assert_eq!(result.unwrap(),if same{d}else{d+1})}
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);let write=good&&!same&&j==d;
 assert_eq!(idx[j],if write{index}else{before_i[j]});let expected=if write{leaf[k]}else{before_v[j][k]};
 #[cfg(not(NKB_invert))] assert_eq!(val[j][k],expected);
 #[cfg(NKB_invert)] assert_ne!(val[j][k],expected);
}

fn forbidden_verify<H:Digest32>(_:H,_:Arity,_:&[u8;32],_:&mut[u32;16],_:&mut[[u8;32];16],_:usize,_:&[u8])->bool{assert!(false,"no verify after nonzero first padding word");false}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(multiproof::verify_in_place,forbidden_verify)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn padding_first(){
 let proof:[u8;57607]=kani::any();let s:usize=kani::any();let count:usize=kani::any();kani::assume(s<6);kani::assume(count<SLOT_NODES[s]);
 let nonzero:usize=kani::any();kani::assume(nonzero<8);let start=compact::slot_offset(s)+32*count;kani::assume(proof[start+nonzero]!=0);
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let d:usize=kani::any();kani::assume(d<=16);let root:[u8;32]=kani::any();
 let out=padding_fragment(&proof,root,s,&mut idx,&mut val,d,NoDigest,count);
 #[cfg(not(NKB_invert))] assert!(matches!(out,Err(Error::Parse)));
 #[cfg(NKB_invert)] assert!(!matches!(out,Err(Error::Parse)));
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);assert_eq!(idx[j],before_i[j]);assert_eq!(val[j][k],before_v[j][k]);
}

#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn padding_word(){
 let word:[u8;8]=kani::any();let out=padding_word_fragment(&word);let expected=word!=[0u8;8];
 #[cfg(not(NKB_invert))] assert_eq!(out,expected);
 #[cfg(NKB_invert)] assert_ne!(out,expected);
}

// Standard-library fidelity: ONE ChunksExact::next on arbitrary remaining length.
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn chunks_next(){
 let bytes:[u8;5504]=kani::any();let len:usize=kani::any();kani::assume(len<=5504);
 let mut iter=bytes[..len].chunks_exact(8);let rem_ptr=iter.remainder().as_ptr();let rem_len=iter.remainder().len();let before=iter.len();let next=iter.next();
 assert_eq!(before,len/8);assert_eq!(rem_len,len%8);assert_eq!(iter.remainder().as_ptr(),rem_ptr);assert_eq!(iter.remainder().len(),rem_len);
 #[cfg(not(NKB_invert))] assert_eq!(next.is_some(),len>=8);
 #[cfg(NKB_invert)] assert_ne!(next.is_some(),len>=8);
 if let Some(word)=next{assert_eq!(word.len(),8);assert_eq!(word.as_ptr(),bytes.as_ptr());let j:usize=kani::any();kani::assume(j<8);assert_eq!(word[j],bytes[j]);assert_eq!(iter.len(),before-1)}else{assert_eq!(iter.len(),0)}
}

#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn parse_exit(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let out=parse_exit_fragment(&mut idx,&mut val);
 #[cfg(not(NKB_invert))] assert!(matches!(out,Err(Error::Parse)));
 #[cfg(NKB_invert)] assert!(!matches!(out,Err(Error::Parse)));
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);assert_eq!(idx[j],before_i[j]);assert_eq!(val[j][k],before_v[j][k]);
}

// Kit-method-3 differential: actual std any, at most ONE complete chunk.
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn any_one_chunk(){
 let bytes:[u8;15]=kani::any();let len:usize=kani::any();kani::assume(len<=15);let mut iter=bytes[..len].chunks_exact(8);let remainder=iter.remainder();let calls=core::cell::Cell::new(0usize);
 let out=iter.any(|w|{calls.set(calls.get()+1);u64::from_le_bytes(w.try_into().unwrap()) != 0});
 let expected=if len<8{false}else{bytes[..8]!=[0u8;8]};
 assert_eq!(calls.get(),len/8);assert_eq!(iter.len(),0);assert_eq!(iter.remainder().as_ptr(),remainder.as_ptr());assert_eq!(iter.remainder().len(),remainder.len());
 #[cfg(not(NKB_invert))] assert_eq!(out,expected);
 #[cfg(NKB_invert)] assert_ne!(out,expected);
}
