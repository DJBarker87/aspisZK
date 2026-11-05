from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
s='''use super::*;
impl QueryScan {
 fn NHB_at_block_end(&mut self,block:&[u8;32])->bool {
  let mut iterator=query_words(block).into_iter();
  let _=iterator.nth(7);
  for candidate in iterator {
'''+body+'''
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
'''
(E/'NHB_block_end.rs.txt').write_text(s)
(E/'NHB_BLOCK_END.json').write_text(json.dumps(dict(word_body_sha256=hashlib.sha256(body.encode()).hexdigest(),cursor=8,prestate='arbitrary scan with len<=22,draws<=64, arbitrary block/window',wrong_control='insert a full/draw stop check after the last word; must fail at full state',callee_value='native membership body unreachable; no value stub'),indent=2)+'\n')
