from NCB_generate import *
name='programs/r1-cost-probe/src/lib.rs'
s=current(name)
# Verbatim validated replacement bodies; no new copy implementation.
k=(I/'NBS_KMX_KMX_copy_stubs.patch').read_text().split('diff --git a/KMX_native.rs',1)[0]
stub=''.join(l[1:] for l in k.splitlines(True) if l.startswith('+') and not l.startswith('+++')).split('#[cfg(kani)]',1)[0]
s2=s+'\n#[cfg(kani)] mod NCB_copy {\n'+stub+'\n}\n'
s2=s2.replace('//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.','//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.\n#![cfg_attr(kani, feature(allocator_api))]',1)
text=r'''
#[cfg(kani)] mod NCB_digest {
 use super::*;
 use aspis_core::Digest32;
 static mut PARTS:*const &[u8]=core::ptr::null();static mut LEN:usize=0;
 static mut REPLY:[u8;32]=[0;32];static mut CALLS:usize=0;
 fn reply(parts:&[&[u8]])->solana_program::hash::Hash {unsafe{
  assert!(CALLS==0);CALLS=1;
  assert!(parts.len()==LEN);assert!(core::ptr::eq(parts.as_ptr(),PARTS));
  solana_program::hash::Hash::new_from_array(REPLY)
 }}
 #[kani::proof] #[kani::unwind(64)]
 ATTR #[kani::stub(hashv,reply)]
 fn routing(){
  let a:[u8;4]=kani::any();let b:[u8;4]=kani::any();let c:[u8;4]=kani::any();
  let la:usize=kani::any();let lb:usize=kani::any();let lc:usize=kani::any();
  kani::assume(la<=4&&lb<=4&&lc<=4);let all=[&a[..la],&b[..lb],&c[..lc]];
  let n:usize=kani::any();kani::assume(n<=3);let parts=&all[..n];let result:[u8;32]=kani::any();
  unsafe{PARTS=parts.as_ptr();LEN=parts.len();REPLY=result;CALLS=0;}
  let out=SolanaDigest.digest(parts);let j:usize=kani::any();kani::assume(j<32);
  assert!(out[j]==result[j]);unsafe{assert!(CALLS==1);}
 }
 #[kani::proof] #[kani::unwind(32)]
 ATTR fn copy_negative(){
  let a:[u32;16]=[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,512];let mut b=[0u32;16];b.copy_from_slice(&a);assert!(b[15]==0);
 }
}
'''.replace('ATTR',attrs.replace('crate::NBS_copy','crate::NCB_copy'))
s2+=text
(E/'NCB_digest.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),s2.splitlines(True),fromfile='a/'+name,tofile='b/'+name)))
