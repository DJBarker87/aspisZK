use super::*;
impl QueryScan {
 fn NHB_direct_word(&mut self,candidate:u32)->bool {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
 false
 }
 fn NHB_direct_cursor(&mut self,block:&[u8;32],cursor:&mut usize)->(bool,u32) {
  let mut iterator=query_words(block).into_iter();
  if *cursor>0 {let _=iterator.nth(*cursor-1);}
  let candidate=iterator.next().unwrap();*cursor+=1;
  (self.NHB_direct_word(candidate),candidate)
 }
}
fn NHB_natural_member(accepted:&[u32;22],len:usize,candidate:u32)->bool {(len>0 && accepted[0]==candidate) || (len>1 && accepted[1]==candidate) || (len>2 && accepted[2]==candidate) || (len>3 && accepted[3]==candidate) || (len>4 && accepted[4]==candidate) || (len>5 && accepted[5]==candidate) || (len>6 && accepted[6]==candidate) || (len>7 && accepted[7]==candidate) || (len>8 && accepted[8]==candidate) || (len>9 && accepted[9]==candidate) || (len>10 && accepted[10]==candidate) || (len>11 && accepted[11]==candidate) || (len>12 && accepted[12]==candidate) || (len>13 && accepted[13]==candidate) || (len>14 && accepted[14]==candidate) || (len>15 && accepted[15]==candidate) || (len>16 && accepted[16]==candidate) || (len>17 && accepted[17]==candidate) || (len>18 && accepted[18]==candidate) || (len>19 && accepted[19]==candidate) || (len>20 && accepted[20]==candidate) || (len>21 && accepted[21]==candidate)}
fn NHB_scalar_ref(len:usize,draws:usize,start:usize,window:usize,old_value:u32,candidate:u32,member:bool)
 ->(bool,u32,usize,usize,usize,u32) {
 let halted=len==22 || draws==64;
 (halted,candidate,start+1,if halted || member {len}else{len+1},if halted{draws}else{draws+1},
 if !halted && !member && window==len {candidate}else{old_value})
}
#[kani::requires(len<=22 && draws<=64 && start<8 && window<22 && accepted[0]<(1<<18) && accepted[1]<(1<<18) && accepted[2]<(1<<18) && accepted[3]<(1<<18) && accepted[4]<(1<<18) && accepted[5]<(1<<18) && accepted[6]<(1<<18) && accepted[7]<(1<<18) && accepted[8]<(1<<18) && accepted[9]<(1<<18) && accepted[10]<(1<<18) && accepted[11]<(1<<18) && accepted[12]<(1<<18) && accepted[13]<(1<<18) && accepted[14]<(1<<18) && accepted[15]<(1<<18) && accepted[16]<(1<<18) && accepted[17]<(1<<18) && accepted[18]<(1<<18) && accepted[19]<(1<<18) && accepted[20]<(1<<18) && accepted[21]<(1<<18) && (len>0 || accepted[0]==0) && (len>1 || accepted[1]==0) && (len>2 || accepted[2]==0) && (len>3 || accepted[3]==0) && (len>4 || accepted[4]==0) && (len>5 || accepted[5]==0) && (len>6 || accepted[6]==0) && (len>7 || accepted[7]==0) && (len>8 || accepted[8]==0) && (len>9 || accepted[9]==0) && (len>10 || accepted[10]==0) && (len>11 || accepted[11]==0) && (len>12 || accepted[12]==0) && (len>13 || accepted[13]==0) && (len>14 || accepted[14]==0) && (len>15 || accepted[15]==0) && (len>16 || accepted[16]==0) && (len>17 || accepted[17]==0) && (len>18 || accepted[18]==0) && (len>19 || accepted[19]==0) && (len>20 || accepted[20]==0) && (len>21 || accepted[21]==0) && old_value==accepted[window] && candidate==(u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1)) && member==NHB_natural_member(&accepted,len,candidate))]
#[kani::ensures(|out| *out==NHB_scalar_ref(len,draws,start,window,old_value,candidate,member))]
fn NHB_native_word(accepted:[u32;22],len:usize,draws:usize,block:[u8;32],start:usize,window:usize,
 old_value:u32,candidate:u32,member:bool)->(bool,u32,usize,usize,usize,u32) {
 let mut copied=block;
 #[cfg(NHB_reply_corrupt)] {copied[0]^=1;}
 let mut scan=QueryScan{accepted,accepted_len:len,draws};let mut cursor=start;
 let (stop,word)=scan.NHB_direct_cursor(&copied,&mut cursor);
 (stop,word,cursor,scan.accepted_len,scan.draws,scan.accepted[window])
}
#[kani::proof_for_contract(NHB_native_word)] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_native_word_contract() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let start:usize=kani::any();let window:usize=kani::any();
 let old_value:u32=kani::any();let candidate:u32=kani::any();let member:bool=kani::any();
 NHB_native_word(accepted,len,draws,block,start,window,old_value,candidate,member);
}
