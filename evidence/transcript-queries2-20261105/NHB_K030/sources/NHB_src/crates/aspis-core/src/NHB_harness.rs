use super::*;
fn NHB_cursor_read(block:&[u8;32], cursor:&mut usize)->Option<u32> {
 let mut iterator=query_words(block).into_iter();
 if *cursor>0 {let _=iterator.nth(*cursor-1);}
 let word=iterator.next();
 if word.is_some() {*cursor+=1;}
 word
}
#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_cursor_read_frame() {
 let block:[u8;32]=kani::any();let start:usize=kani::any();kani::assume(start<=8);
 let expected=if start<8 {
  Some(u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1))
 } else {None};
 let mut copied=block;
 #[cfg(NHB_invert)] {copied[0]^=1;}
 let mut cursor=start;let word=NHB_cursor_read(&copied,&mut cursor);
 assert!(word==expected && cursor==if start<8 {start+1} else {start});
}
