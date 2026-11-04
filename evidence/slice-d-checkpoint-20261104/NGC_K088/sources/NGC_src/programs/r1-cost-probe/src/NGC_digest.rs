use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{outer:*const &'a[u8],count:usize,index:usize,part:*const u8,length:usize,calls:u8,reply:[u8;32]}
fn hashv_window<'a>(parts:&[&'a[u8]],log:&mut Log<'a>)->solana_program::hash::Hash{
 log.outer=parts.as_ptr();log.count=parts.len();log.calls+=1;
 if log.index<parts.len(){log.part=parts[log.index].as_ptr();log.length=parts[log.index].len();}
 solana_program::hash::Hash::new_from_array(log.reply)
}
// Literal digest expression, with only its syscall boundary instrumented.
fn digest_window<'a>(parts:&[&'a[u8]],log:&mut Log<'a>)->[u8;32]{hashv_window(parts,log).to_bytes()}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn digest_forward(){let b0:[u8;57607]=kani::any();let b1:[u8;57607]=kani::any();let b2:[u8;57607]=kani::any();let b3:[u8;57607]=kani::any();let b4:[u8;57607]=kani::any();let b5:[u8;57607]=kani::any();let b6:[u8;57607]=kani::any();let b7:[u8;57607]=kani::any();let b8:[u8;57607]=kani::any();let lengths:[usize;9]=kani::any();for j in 0..9{kani::assume(lengths[j]<=57607);}let parts=[&b0[..lengths[0]],&b1[..lengths[1]],&b2[..lengths[2]],&b3[..lengths[3]],&b4[..lengths[4]],&b5[..lengths[5]],&b6[..lengths[6]],&b7[..lengths[7]],&b8[..lengths[8]]];let n:usize=kani::any();kani::assume(n<=9);let i:usize=kani::any();kani::assume(i<9);let reply:[u8;32]=kani::any();let mut log=Log{outer:core::ptr::null(),count:99,index:i,part:core::ptr::null(),length:99,calls:0,reply};let got=digest_window(&parts[..n],&mut log);assert!(log.calls==1&&log.outer==parts.as_ptr()&&log.count==n);if i<n{assert!(log.part==parts[i].as_ptr()&&log.length==parts[i].len());}assert!((got==reply)!=cfg!(NGC_invert));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn digest_copy_positive(){let src:[u8;32]=kani::any();let h=solana_program::hash::Hash::new_from_array(src);let out=h.to_bytes();let i:usize=kani::any();kani::assume(i<32);assert!(out[i]==src[i]);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn digest_copy_negative(){let src:[u8;32]=kani::any();let h=solana_program::hash::Hash::new_from_array(src);let out=h.to_bytes();let i:usize=kani::any();kani::assume(i<32);assert!(out[i]!=src[i]);}
