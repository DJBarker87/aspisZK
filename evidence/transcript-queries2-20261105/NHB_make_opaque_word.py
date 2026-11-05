from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
old='self.accepted[..self.accepted_len].contains(&candidate)';new='NHB_member_logged(&self.accepted[..self.accepted_len],&candidate,self.draws,reply,window,log)'
assert body.count(old)==1
s='''use super::*;
#[derive(Default)] struct NHB_Log {count:usize,len:usize,candidate:u32,draws:usize,cell:Option<u32>}
fn NHB_member_logged(prefix:&[u32],candidate:&u32,draws:usize,reply:bool,window:usize,log:&mut NHB_Log)->bool {
 log.count+=1;log.len=prefix.len();log.candidate=*candidate;log.draws=draws;
 log.cell=if window<prefix.len(){Some(prefix[window])}else{None};reply
}
impl QueryScan {
 fn NHB_word_log(&mut self,candidate:u32,reply:bool,window:usize,log:&mut NHB_Log)->bool {
'''+body.replace(old,new)+'''
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
'''
(E/'NHB_opaque_word.rs.txt').write_text(s)
(E/'NHB_OPAQUE_WORD.json').write_text(json.dumps(dict(body_sha256=hashlib.sha256(body.encode()).hexdigest(),callee_call_erasure=body.replace(old,new).replace(new,old)==body,domain='all bounded scan states, arbitrary block, cursor<8, arbitrary returned Bool',status='CONDITIONAL caller window; does not prove native membership value',missing='native Std.contains reply equals coherent predicate for lengths11..21',control='exact copied block byte0; all log state local by &mut'),indent=2)+'\n')
