use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{reply:[u8;32],calls:usize,parts:Option<&'a[&'a[u8]]>}
// Exact frozen expression. The call cut records the ACTUAL typed immutable
// borrow, whose lifetime is the input lifetime. No buffer is read or written;
// no reference or guard is fabricated from integers or bytes.
fn syscall_cut<'a>(parts:&'a[&'a[u8]],log:&mut Log<'a>)->[u8;32]{
 let mut hashv=|xs:&'a[&'a[u8]]|{log.calls+=1;log.parts=Some(if cfg!(NFW_badarg){&xs[1..]}else{xs});Hash::new_from_array(log.reply)};
 hashv(parts).to_bytes()
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 let mut data=[[0u8;57607];5];let chosen:usize=kani::any();let offset:usize=kani::any();let value:u8=kani::any();kani::assume(chosen<5&&offset<57607);data[chosen][offset]=value;let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=57607);i+=1;}
 let count:usize=kani::any();kani::assume(count>=1&&count<=5&&chosen<count);kani::assume(offset<lengths[chosen]);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];
 let input=&parts[..count];let mut log=Log{reply:kani::any(),calls:0,parts:None};
 let result=syscall_cut(input,&mut log);let word:usize=kani::any();kani::assume(word<32);
 assert_eq!(log.calls,1);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 assert!(core::ptr::eq(log.parts.unwrap(),input));assert_eq!(log.parts.unwrap()[chosen][offset],value);
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_hash(){let src=Hash::new_from_array(kani::any());let mut dst=Hash::new_from_array(kani::any());unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst.to_bytes()[word]==src.to_bytes()[word])!=cfg!(NFW_invert));}
