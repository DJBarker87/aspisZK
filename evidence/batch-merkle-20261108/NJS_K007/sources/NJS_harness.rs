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
struct LeafOracle<'a> { value: &'a [u8], salt: &'a [u8;32], tag:u8, byte:usize, reply:[u8;32], count:&'a core::cell::Cell<usize> }
impl aspis_core::Digest32 for LeafOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(self.count.get(),0);self.count.set(1);
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),2);assert_eq!(parts[0][0],0x10);assert_eq!(parts[0][1],self.tag);
  assert_eq!(parts[1].len(),self.value.len());assert_eq!(parts[1].as_ptr(),self.value.as_ptr());
  if !self.value.is_empty(){assert_eq!(parts[1][self.byte],self.value[self.byte]);}
  assert_eq!(parts[2].len(),32);assert_eq!(parts[2].as_ptr(),self.salt.as_ptr());assert_eq!(parts[2][self.byte%32],self.salt[self.byte%32]);
  self.reply
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn private_leaf() {
 let value:[u8;480]=kani::any();let salt:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let tag:u8=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n<=480);kani::assume(k<core::cmp::max(n,1));
 let calls=core::cell::Cell::new(0);let hash=LeafOracle{value:&value[..n],salt:&salt,tag,byte:k,reply,count:&calls};
 let actual=aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,tag,&value[..n],&salt);
 assert_eq!(calls.get(),1);
 let out:usize=kani::any();kani::assume(out<32);
 #[cfg(not(NJS_invert))] assert_eq!(actual[out],reply[out]);
 #[cfg(NJS_invert)] assert_ne!(actual[out],reply[out]);
}
