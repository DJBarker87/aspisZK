use super::*;
#[derive(Default)] struct NHB_Log {count:usize,len:usize,candidate:u32,draws:usize,cell:Option<u32>}
fn NHB_member_logged(prefix:&[u32],candidate:&u32,draws:usize,reply:bool,window:usize,log:&mut NHB_Log)->bool {
 log.count+=1;log.len=prefix.len();log.candidate=*candidate;log.draws=draws;
 log.cell=if window<prefix.len(){Some(prefix[window])}else{None};reply
}
impl QueryScan {
 fn NHB_word_log(&mut self,candidate:u32,reply:bool,window:usize,log:&mut NHB_Log)->bool {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !NHB_member_logged(&self.accepted[..self.accepted_len],&candidate,self.draws,reply,window,log) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
 false
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_opaque_word_frame() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let start:usize=kani::any();let window:usize=kani::any();let reply:bool=kani::any();
 kani::assume(len<=22 && draws<=64 && start<8 && window<22);
 let candidate=u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1);
 let halted=len==22 || draws==64;let expected_word=if !halted && !reply && window==len{candidate}else{accepted[window]};
 let expected_len=if halted || reply{len}else{len+1};let expected_draws=if halted{draws}else{draws+1};
 let prefix_word=if window<len {Some(accepted[window])}else{None};
 let mut copied=block;
 #[cfg(NHB_invert)] {copied[0]^=1;}
 let mut iterator=query_words(&copied).into_iter();if start>0{let _=iterator.nth(start-1);}
 let actual_word=iterator.next().unwrap();let remaining=iterator.len();let mut log=NHB_Log::default();
 let mut scan=QueryScan{accepted,accepted_len:len,draws};let stop=scan.NHB_word_log(actual_word,reply,window,&mut log);
 let log_correct=if halted {log.count==0 && log.len==0 && log.candidate==0 && log.draws==0 && log.cell==None}
 else {log.count==1 && log.len==len && log.candidate==candidate && log.draws==draws+1 && log.cell==prefix_word};
 assert!(actual_word==candidate && remaining==7-start && stop==halted && scan.accepted_len==expected_len && scan.draws==expected_draws && scan.accepted[window]==expected_word && log_correct);
}
