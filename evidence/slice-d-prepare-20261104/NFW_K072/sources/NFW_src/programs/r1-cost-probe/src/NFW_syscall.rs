use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{reply:[u8;32],calls:usize,parts:Option<&'a[&'a[u8]]>}
// Frozen expression; only the runtime call is a local-record cut. The corrupt
// argument control changes the actual call argument, not the recording code.
fn syscall_cut<'a>(parts:&'a[&'a[u8]],log:&mut Log<'a>)->[u8;32]{let mut hashv=|xs:&'a[&'a[u8]]|{log.calls+=1;log.parts=Some(xs);Hash::new_from_array(log.reply)};hashv(if cfg!(NFW_badarg)&&!parts.is_empty(){&parts[1..]}else{parts}).to_bytes()}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 const WIDTH:usize=32;
 let data:[[u8;WIDTH];5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=WIDTH);i+=1;}
 let count:usize=if cfg!(NFW_badarg)||cfg!(NFW_invert){1}else{kani::any()};kani::assume(count<=5);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];let input=&parts[..count];
 let mut log=Log{reply:kani::any(),calls:0,parts:None};let result=syscall_cut(input,&mut log);let word:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(word<32);
 assert_eq!(log.calls,1);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 let seen=log.parts.unwrap();let same=seen.len()==input.len()&&core::ptr::eq(seen,input);assert!(same);
 if same&&count>0{let part:usize=if cfg!(NFW_badarg){0}else{kani::any()};kani::assume(part<count);let at:usize=kani::any();let expected=if at<lengths[part]{data[part][at]}else{0};let actual=if at<seen[part].len(){seen[part][at]}else{0};assert_eq!(actual,expected);}
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_hash(){let src=Hash::new_from_array(kani::any());let mut dst=Hash::new_from_array(kani::any());unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst.to_bytes()[word]==src.to_bytes()[word])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn hash_value(){let reply:[u8;32]=kani::any();let value=Hash::new_from_array(reply).to_bytes();let word:usize=kani::any();kani::assume(word<32);assert!((value[word]==reply[word])!=cfg!(NFW_invert));}
