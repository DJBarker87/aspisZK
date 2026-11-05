"""Explicit ah native contract for the mechanically isolated word body.
The caller's already-checked decode/cursor cut supplies candidate. No aggregate
any return, saved-array snapshot, field product, writable static or new copy stub.
"""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
old='self.accepted[..self.accepted_len].contains(&candidate)';new='NHK_member_logged(&self.accepted[..self.accepted_len],&candidate,self.draws,reply,window,log)'
assert body.count(old)==1
s='''use super::*;
#[derive(Default)] struct NHK_Log {count:usize,len:usize,candidate:u32,draws:usize,cell:Option<u32>}
fn NHK_member_logged(prefix:&[u32],candidate:&u32,draws:usize,reply:bool,window:usize,log:&mut NHK_Log)->bool {
 log.count+=1;log.len=prefix.len();log.candidate=*candidate;log.draws=draws;
 log.cell=if window<prefix.len(){Some(prefix[window])}else{None};reply
}
impl QueryScan {
 fn NHK_word_log(&mut self,candidate:u32,reply:bool,window:usize,log:&mut NHK_Log)->bool {
'''+body.replace(old,new)+'''
 false
 }
}
fn NHK_word_ref(n:usize,d:usize,old:u32,candidate:u32,reply:bool,window:usize)->(bool,usize,usize,u32) {
 let halt=n==22 || d==64;
 (halt,if halt || reply{n}else{n+1},if halt{d}else{d+1},if !halt && !reply && window==n{candidate}else{old})
}
#[kani::requires(scan.accepted_len<=22 && scan.draws<=64 && window<22 &&
 n==scan.accepted_len && d==scan.draws && old==scan.accepted[window] &&
 log.count==0 && log.len==0 && log.candidate==0 && log.draws==0 && log.cell==None)]
#[kani::modifies(scan,log)]
#[kani::ensures(|out| {
 let expected=NHK_word_ref(n,d,old,candidate,reply,window);let halt=expected.0;
 *out==expected.0 && scan.accepted_len==expected.1 && scan.draws==expected.2 && scan.accepted[window]==expected.3 &&
 (if halt {log.count==0 && log.len==0 && log.candidate==0 && log.draws==0 && log.cell==None}
 else {log.count==1 && log.len==n && log.candidate==candidate && log.draws==d+1 && log.cell==(if window<n{Some(old)}else{None})})
})]
fn NHK_word_step(scan:&mut QueryScan,candidate:u32,reply:bool,window:usize,n:usize,d:usize,old:u32,log:&mut NHK_Log)->bool {
 let result=scan.NHK_word_log(candidate,reply,window,log);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof_for_contract(NHK_word_step)] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_word_step_contract() {
 let accepted:[u32;22]=[SCALARS];let len:usize=kani::any();let draws:usize=kani::any();
 let candidate:u32=kani::any();let reply:bool=kani::any();let window:usize=kani::any();
 kani::assume(len<=22 && draws<=64 && window<22);
 let old=accepted[window];let mut log=NHK_Log::default();
 let mut scan=QueryScan{accepted,accepted_len:len,draws};
 NHK_word_step(&mut scan,candidate,reply,window,len,draws,old,&mut log);
}
'''.replace('SCALARS',', '.join(['kani::any()']*22))
(E/'NHK_constant_contains.rs.txt').write_text(s)
(E/'NHK_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(shape='explicit native ah one-word G contract, complete local record and modifies',domain='arbitrary22 raw u32 cells, len<=22, draws<=64, window<22, arbitrary membership reply; pre-observation scalars uniquely available; fresh local ghost log',reference='NHK_word_ref, paired with NHK_WordAssociation.G',frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),reverse_oracle_erasure=body.replace(old,new).replace(new,old)==body,child_value='complete NHK_MEMBERSHIP_CALLEES table; not assumed correct in caller certificate',cursor='retained NHB_K030/031 and K053/054 same block/next association',external_modifies='only scan and fresh local log; full scan frame by arbitrary window'),indent=2)+'\n')
