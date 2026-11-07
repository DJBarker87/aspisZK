extern crate alloc;
use super::*;
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[repr(C)]
struct Context<'a>{parts:[&'a[u8];9],count:usize,outer:*const &'a[u8],reply:[u8;32],calls:Cell<u8>}
fn hashv_reply(parts:&[&[u8]])->solana_program::hash::Hash{
 let c=unsafe{&*(parts.as_ptr() as *const Context<'_>)};
 assert_eq!(parts.as_ptr(),c.outer);assert_eq!(parts.len(),c.count);c.calls.set(c.calls.get()+1);
 solana_program::hash::Hash::new_from_array(c.reply)
}
#[kani::proof] #[kani::unwind(200)]
#[kani::stub(solana_program::hash::hashv,hashv_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn digest_forward(){
 let a:[u8;57607]=kani::any();let b:[u8;57607]=kani::any();let d:[u8;57607]=kani::any();let e:[u8;57607]=kani::any();let f:[u8;57607]=kani::any();let g:[u8;57607]=kani::any();let h:[u8;57607]=kani::any();let i:[u8;57607]=kani::any();let j:[u8;57607]=kani::any();
 let lengths:[usize;9]=kani::any();for k in 0..9{kani::assume(lengths[k]<=57607);}let n:usize=kani::any();kani::assume(n<=9);
 let mut c=Context{parts:[&a[..lengths[0]],&b[..lengths[1]],&d[..lengths[2]],&e[..lengths[3]],&f[..lengths[4]],&g[..lengths[5]],&h[..lengths[6]],&i[..lengths[7]],&j[..lengths[8]]],count:n,outer:core::ptr::null(),reply:kani::any(),calls:Cell::new(0)};c.outer=c.parts.as_ptr();
 let got=solana_sha256(&c.parts[..n]);assert_eq!(c.calls.get(),1);assert!((got==c.reply)!=cfg!(PCG_NEG_DIGEST));
}
