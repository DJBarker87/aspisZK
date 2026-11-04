use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log {reply:[u8;32],calls:usize,count:usize,lengths:[usize;5],observed:u8,position:usize,selected:usize}
// Exact frozen wrapper expression, with only the runtime hashv call cut to an
// explicit local record. SHA values remain the accepted runtime trust row.
fn syscall_cut(parts:&[&[u8]],log:&mut Log)->[u8;32]{
 let mut hashv=|xs:&[&[u8]]|{log.calls+=1;log.count=xs.len();let mut i=0;while i<xs.len(){log.lengths[i]=xs[i].len();i+=1;}let j=log.position;let target=xs[log.selected];log.observed=if j<target.len(){target[j]}else{0};Hash::new_from_array(log.reply)};
 hashv(parts).to_bytes()
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 let data:[[u8;57607];5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=57607);i+=1;}
 let count:usize=kani::any();kani::assume(count<=5);let selected=if cfg!(NFW_part0){0}else if cfg!(NFW_part1){1}else if cfg!(NFW_part2){2}else if cfg!(NFW_part3){3}else{4};kani::assume(selected<count);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];
 let mut log=Log{reply:kani::any(),calls:0,count:0,lengths:[0;5],observed:0,position:kani::any(),selected};
 let result=syscall_cut(&parts[..count],&mut log);let word:usize=kani::any();kani::assume(word<32);
 assert_eq!(log.calls,1);assert_eq!(log.count,count);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 let part=selected;assert_eq!(log.lengths[part],lengths[part]);let at=log.position;
 let expected=if at<lengths[part]{data[part][at]}else{0};assert!((log.observed==expected)!=cfg!(NFW_badarg));
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_hash(){let src=Hash::new_from_array(kani::any());let mut dst=Hash::new_from_array(kani::any());unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst.to_bytes()[word]==src.to_bytes()[word])!=cfg!(NFW_invert));}
