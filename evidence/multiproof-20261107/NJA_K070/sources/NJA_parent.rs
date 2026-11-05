use super::*;
use aspis_core::Digest32;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct NJA_Log{calls:usize,reply:[u8;32],k:usize,left:u8,right:u8}
fn NJA_digest(log:&mut NJA_Log,_hash:SolanaDigest,parts:&[&[u8]])->[u8;32]{
 assert_eq!(log.calls,0);assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),1);assert_eq!(parts[0][0],0x12);assert_eq!(parts[1].len(),32);assert_eq!(parts[2].len(),32);
 assert_eq!(parts[1][log.k],log.left);assert_eq!(parts[2][log.k],log.right);log.calls+=1;log.reply
}
// Concrete deployed SolanaDigest instance, with one explicit local opaque log.
// Removing the log parameter and restoring the Digest32 call gives the exact
// frozen helper body; arithmetic/digest values are never verified here.
fn NJA_occupied(log:&mut NJA_Log,hash:SolanaDigest,values:&[[u8;32];16],index:usize)->[u8;32]{NJA_digest(log,hash,&[&[0x12],&values[index],&values[index+1]])}
fn NJA_sibling(log:&mut NJA_Log,hash:SolanaDigest,values:&[[u8;32];16],index:usize,sibling:&[u8],left:bool)->[u8;32]{
 if left{NJA_digest(log,hash,&[&[0x12],&values[index],sibling])}else{NJA_digest(log,hash,&[&[0x12],sibling,&values[index]])}
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_copy(){let src:[u8;128]=kani::any();let mut dst=[0u8;128];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),128)};let k:usize=kani::any();kani::assume(k<128);if cfg!(NJA_bad_argument){assert_eq!(dst[k],src[k]^1)}else{assert_eq!(dst[k],src[k])}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_occupied_log(){let values:[[u8;32];16]=kani::any();let i:usize=kani::any();let k:usize=kani::any();kani::assume(i<15&&k<32);let mut log=NJA_Log{calls:0,reply:kani::any(),k,left:values[i][k],right:values[i+1][k]};if cfg!(NJA_bad_argument){log.left^=1;}let before=log.reply[k];let out=NJA_occupied(&mut log,SolanaDigest,&values,i);assert_eq!(log.calls,1);assert_eq!(out[k],before);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_sibling_log(){let values:[[u8;32];16]=kani::any();let sibling:[u8;32]=kani::any();let i:usize=kani::any();let k:usize=kani::any();let left:bool=kani::any();kani::assume(i<16&&k<32);let l=if left{values[i][k]}else{sibling[k]};let r=if left{sibling[k]}else{values[i][k]};let mut log=NJA_Log{calls:0,reply:kani::any(),k,left:l,right:r};if cfg!(NJA_bad_argument){log.left^=1;}let before=log.reply[k];let out=NJA_sibling(&mut log,SolanaDigest,&values,i,&sibling,left);assert_eq!(log.calls,1);assert_eq!(out[k],before);}
