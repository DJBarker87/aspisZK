use super::*;
impl QueryScan {
 fn NHB_at_block_end(&mut self,block:&[u8;32])->bool {
  let mut iterator=query_words(block).into_iter();
  let _=iterator.nth(7);
  for candidate in iterator {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
  }
  #[cfg(not(NHB_invert))] {false}
  #[cfg(NHB_invert)] {self.accepted_len==QUERY_COUNT || self.draws==QUERY_MAX_DRAWS}
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_block_end_frame() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let window:usize=kani::any();
 kani::assume(len<=22 && draws<=64 && window<22);
 let expected=accepted[window];let mut scan=QueryScan{accepted,accepted_len:len,draws};
 let stop=scan.NHB_at_block_end(&block);
 assert!(!stop && scan.accepted_len==len && scan.draws==draws && scan.accepted[window]==expected);
}
