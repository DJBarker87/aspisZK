use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn key_at() {
 let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);
 let actual=batch_key_at(&keys,i);
 #[cfg(not(NJS_invert))] assert_eq!(actual,keys[i]);
 #[cfg(NJS_invert)] assert_ne!(actual,keys[i]);
}
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn same_index() {
 let values:[u32;16]=kani::any();let i:usize=kani::any();let expected:u32=kani::any();kani::assume(i<16);
 let actual=same_batch_index(&values,i,expected);
 #[cfg(not(NJS_invert))] assert_eq!(actual,values[i]==expected);
 #[cfg(NJS_invert)] assert_ne!(actual,values[i]==expected);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn same_leaf() {
 let values:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<16);
 let actual=same_batch_leaf(&values,i,leaf);
 #[cfg(not(NJS_invert))] assert_eq!(actual,values[i]==leaf);
 #[cfg(NJS_invert)] assert_ne!(actual,values[i]==leaf);
}
#[derive(Clone,Copy)]
struct LeafOracle<'a> { value: &'a [u8], salt: &'a [u8;32], tag:u8, byte:usize, salt_byte:usize, reply:[u8;32], count:&'a core::cell::Cell<usize> }
impl aspis_core::Digest32 for LeafOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(self.count.get(),0);self.count.set(1);
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),2);assert_eq!(parts[0][0],0x10);assert_eq!(parts[0][1],self.tag);
  assert_eq!(parts[1].len(),self.value.len());assert_eq!(parts[1].as_ptr(),self.value.as_ptr());
  if !self.value.is_empty(){assert_eq!(parts[1][self.byte],self.value[self.byte]);}
  assert_eq!(parts[2].len(),32);assert_eq!(parts[2].as_ptr(),self.salt.as_ptr());assert_eq!(parts[2][self.salt_byte],self.salt[self.salt_byte]);
  self.reply
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn private_leaf() {
 let value:[u8;480]=kani::any();let salt:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let tag:u8=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n<=480);kani::assume(k<core::cmp::max(n,1));
 let salt_byte:usize=kani::any();kani::assume(salt_byte<32);
 let calls=core::cell::Cell::new(0);let hash=LeafOracle{value:&value[..n],salt:&salt,tag,byte:k,salt_byte,reply,count:&calls};
 let actual=aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,tag,&value[..n],&salt);
 assert_eq!(calls.get(),1);
 let out:usize=kani::any();kani::assume(out<32);
 #[cfg(not(NJS_invert))] assert_eq!(actual[out],reply[out]);
 #[cfg(NJS_invert)] assert_ne!(actual[out],reply[out]);
}
#[derive(Clone,Copy)]
struct ParentOracle<'a> { children:&'a [[u8;32];8], child:usize, byte:usize, reply:[u8;32], count:&'a core::cell::Cell<usize> }
impl aspis_core::Digest32 for ParentOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(self.count.get(),0);self.count.set(1);
  assert_eq!(parts.len(),9);assert_eq!(parts[0].len(),1);assert_eq!(parts[0][0],0x18);
  assert_eq!(parts[self.child+1].len(),32);
  assert_eq!(parts[self.child+1].as_ptr(),self.children[self.child].as_ptr());
  assert_eq!(parts[self.child+1][self.byte],self.children[self.child][self.byte]);
  self.reply
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn parent() {
 let children:[[u8;32];8]=kani::any();let reply:[u8;32]=kani::any();let child:usize=kani::any();let byte:usize=kani::any();kani::assume(child<8);kani::assume(byte<32);
 let calls=core::cell::Cell::new(0);let hash=ParentOracle{children:&children,child,byte,reply,count:&calls};
 let actual=aspis_core::r0::merkle::parent_with_digest(hash,&children);
 assert_eq!(calls.get(),1);
 #[cfg(not(NJS_invert))] assert_eq!(actual[byte],reply[byte]);
 #[cfg(NJS_invert)] assert_ne!(actual[byte],reply[byte]);
}
#[inline(never)]
fn slot_offset_spec(s:usize)->usize {
 assert!(s<=6);
 [28359,33031,37703,41799,47303,52807,57607][s]
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(crate::compact::slot_offset,slot_offset_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn slot_view() {
 let proof:[u8;57607]=kani::any();let s:usize=kani::any();kani::assume(s<6);
 let actual=slot(&proof,s);let start=slot_offset_spec(s);let end=slot_offset_spec(s+1);
 assert_eq!(actual.as_ptr(),proof.as_ptr().wrapping_add(start));
 #[cfg(not(NJS_invert))] assert_eq!(actual.len(),end-start);
 #[cfg(NJS_invert)] assert_ne!(actual.len(),end-start);
}

include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NJS_fragments.rs"));
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn key_iteration_cut(){
 let queries:[u32;22]=kani::any();let before:[u64;16]=kani::any();let lo:usize=kani::any();let n:usize=kani::any();let tree:usize=kani::any();let start:usize=kani::any();let k:usize=kani::any();
 kani::assume(n<=16 && start<=n && lo<=22 && lo+n<=22 && k<16 && tree<3);
 let (after,next,entered)=key_iteration(&queries,lo,n,tree,before,start);
 assert_eq!(entered,start<n);assert_eq!(next,if start<n{start+1}else{start});
 let expected=if start<n && k==start {let u=queries[lo+start];let index=if tree==2{u/4}else{u};(index as u64)*256+start as u64}else{before[k]};
 #[cfg(not(NJS_invert))] assert_eq!(after[k],expected);
 #[cfg(NJS_invert)] assert_ne!(after[k],expected);
}
#[derive(Clone,Copy)]
struct BatchLeafOracle<'a> { q:&'a [u8;832], tree:usize, value_byte:usize, salt_byte:usize, reply:[u8;32], calls:&'a core::cell::Cell<usize> }
impl aspis_core::Digest32 for BatchLeafOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let (tag,vs,ve,ss)=if self.tree==0{(0x71,0,480,608)}else if self.tree==1{(0xf1,480,608,640)}else{(0x72,672,800,800)};
  assert_eq!(self.calls.get(),0);self.calls.set(1);
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),2);assert_eq!(parts[0][0],0x10);assert_eq!(parts[0][1],tag);
  assert_eq!(parts[1].len(),ve-vs);assert_eq!(parts[1].as_ptr(),self.q[vs..].as_ptr());assert_eq!(parts[1][self.value_byte],self.q[vs+self.value_byte]);
  assert_eq!(parts[2].len(),32);#[cfg(not(NJS_invert))] assert_eq!(parts[2][self.salt_byte],self.q[ss+self.salt_byte]);
  #[cfg(NJS_invert)] assert_ne!(parts[2][self.salt_byte],self.q[ss+self.salt_byte]);self.reply
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn batch_leaf_cut(){
 let q:[u8;832]=kani::any();let tree:usize=kani::any();let value_byte:usize=kani::any();let salt_byte:usize=kani::any();let out:usize=kani::any();let reply:[u8;32]=kani::any();
 kani::assume(tree<3&&salt_byte<32&&out<32);kani::assume(value_byte<if tree==0{480}else{128});
 let calls=core::cell::Cell::new(0);let hash=BatchLeafOracle{q:&q,tree,value_byte,salt_byte,reply,calls:&calls};
 let actual=batch_leaf(hash,tree,&q);assert_eq!(calls.get(),1);
 #[cfg(not(NJS_invert))] assert_eq!(actual[out],reply[out]);
 #[cfg(NJS_invert)] assert_ne!(actual[out],reply[out]);
}

#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn sort_iteration_cut(){
 let before:[u64;16]=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<16);
 let (after,next,entered)=sort_iteration(before,j);let go=j>0&&before[j-1]>before[j];
 assert_eq!(entered,go);assert_eq!(next,if go{j-1}else{j});
 let expected=if go&&k==j{before[j-1]}else if go&&k+1==j{before[j]}else{before[k]};
 #[cfg(not(NJS_invert))] assert_eq!(after[k],expected);
 #[cfg(NJS_invert)] assert_ne!(after[k],expected);
}
