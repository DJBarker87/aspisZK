extern crate alloc;
use super::*;
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[repr(C)]
struct Context{pool:Pubkey,encoding:[u8;32],digest:[u8;32],calls:Cell<u8>}
fn hash_reply(parts:&[&[u8]])->solana_program::hash::Hash{
 assert_eq!(parts.len(),3);
 let c=unsafe{&*core::ptr::with_exposed_provenance::<Context>(parts[1].as_ptr() as usize)};
 assert_eq!(parts[0],POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN);assert_eq!(parts[1],c.pool.as_ref());assert_eq!(parts[2],&c.encoding);c.calls.set(c.calls.get()+1);
 solana_program::hash::Hash::new_from_array(c.digest)
}
// Injective byte diagnostic only. The arbitrary child reply is proved by the
// exact source-fission log below, rather than assigning a hash or pack value.
fn pack_probe(digest:&[u8;32])->[u8;32]{let mut out=[0;32];for i in 0..32{out[i]=digest[i]^((i as u8).wrapping_mul(7));}out}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::hash::hashv,hash_reply)]
#[kani::stub(pack_pool_v1_pair_forest_marker_seed_v1,pack_probe)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn marker_arguments(){let c=Context{pool:Pubkey::new_from_array(kani::any()),encoding:kani::any(),digest:kani::any(),calls:Cell::new(0)};let _=core::ptr::addr_of!(c).expose_provenance();let got=pool_v1_pair_forest_marker_seed_v1(&c.pool,&c.encoding);let expected=pack_probe(&c.digest);assert_eq!(c.calls.get(),1);assert!((got==expected)!=cfg!(PCG_NEG_MARKER));}
struct Log{digest:[u8;32],reply:[u8;32],pool:Pubkey,encoding:[u8;32],hash_calls:u8,pack_calls:u8}
fn hash_window(parts:&[&[u8]],log:&mut Log)->solana_program::hash::Hash{assert_eq!(parts.len(),3);assert_eq!(parts[0],POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN);assert_eq!(parts[1],log.pool.as_ref());assert_eq!(parts[2],&log.encoding);log.hash_calls+=1;solana_program::hash::Hash::new_from_array(log.digest)}
fn pack_window(digest:&[u8;32],log:&mut Log)->[u8;32]{assert_eq!(digest,&log.digest);log.pack_calls+=1;log.reply}
fn marker_window(pool:&Pubkey,canonical_nullifier_encoding:&[u8;32],log:&mut Log)->[u8;32]{
 let digest=hash_window(&[POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN,pool.as_ref(),canonical_nullifier_encoding],log).to_bytes();
 pack_window(&digest,log)
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn marker_reply(){let pool=Pubkey::new_from_array(kani::any());let encoding:[u8;32]=kani::any();let mut log=Log{digest:kani::any(),reply:kani::any(),pool,encoding,hash_calls:0,pack_calls:0};let got=marker_window(&pool,&encoding,&mut log);assert_eq!(log.hash_calls,1);assert_eq!(log.pack_calls,1);assert!((got==log.reply)!=cfg!(PCG_NEG_MARKER));}
