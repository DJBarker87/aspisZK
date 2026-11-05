from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
old='self.accepted[..self.accepted_len].contains(&candidate)'
assert body.count(old)==1
cut=body.replace(old,'NHB_member(&self.accepted,self.accepted_len,candidate)')
text='''fn NHB_member(a:&[u32;22], n:usize, x:u32)->bool { match n {
'''+''.join(f'{n} => NHB_contains_{n}(a,n,x),\n' for n in range(23))+'''_ => unreachable!(),
}}
impl QueryScan {
 fn NHB_word(&mut self,candidate:u32)->bool {
'''+cut+'''
 false
 }
 fn NHB_cursor_word(&mut self,block:&[u8;32],cursor:&mut usize)->(bool,u32) {
  let words=query_words(block);
  let mut iterator=words.into_iter();
  if *cursor>0 {let _=iterator.nth(*cursor-1);}
  let candidate=iterator.next().unwrap();
  *cursor+=1;
  (self.NHB_word(candidate),candidate)
 }
}
#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
'''+''.join(f'#[kani::stub_verified(NHB_contains_{n})]\n' for n in range(23))+'''fn NHB_cursor_word_frame() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let start:usize=kani::any();let j:usize=kani::any();
 kani::assume(len<=22 && draws<=64 && start<8 && j<22);
 let candidate=u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1);
 let member=NHB_member(&accepted,len,candidate);
 let halted=len==22 || draws==64;
 let expected_word=if !halted && !member && j==len {candidate} else {accepted[j]};
 let expected_len=if halted || member {len} else {len+1};
 let expected_draws=if halted {draws} else {draws+1};
 let mut copied=block;
 #[cfg(NHB_invert)] {copied[0]^=1;}
 let mut scan=QueryScan{accepted,accepted_len:len,draws};let mut cursor=start;
 let (stop,word)=scan.NHB_cursor_word(&copied,&mut cursor);
 assert!(word==candidate && cursor==start+1 && stop==halted && scan.draws==expected_draws && scan.accepted_len==expected_len && scan.accepted[j]==expected_word);
}
'''
(E/'NHB_word.rs.txt').write_text(text)
(E/'NHB_WORD_CUT.json').write_text(json.dumps(dict(frozen_start_line=src[:a].count('\n')+1,frozen_end_line=src[:b].count('\n')+1,body_sha256=hashlib.sha256(body.encode()).hexdigest(),original_call=old,replacement_call='NHB_member(&self.accepted,self.accepted_len,candidate)',body_erasure_restores_frozen=cut.replace('NHB_member(&self.accepted,self.accepted_len,candidate)',old)==body,domain='len<=22, draws<=64, cursor<8, arbitrary observation j<22; arbitrary block and all22 survivor cells'),indent=2)+'\n')
