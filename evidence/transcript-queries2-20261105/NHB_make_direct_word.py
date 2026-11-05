from pathlib import Path
import json,lzma,hashlib,sys
E=Path(__file__).resolve().parent
mode=sys.argv[1] if len(sys.argv)>1 else 'full'
cases=dict(full='true',stop='(len==22 || draws==64)',low='(draws<64 && len<=10)',mid='(draws<64 && 11<=len && len<=15)',high='(draws<64 && 16<=len && len<22)')
restriction=cases[mode]
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
canon=' && '.join(f'accepted[{i}]<(1<<18)' for i in range(22))
inactive=' && '.join(f'(len>{i} || accepted[{i}]==0)' for i in range(22))
member=' || '.join(f'(len>{i} && accepted[{i}]==candidate)' for i in range(22))
s='''use super::*;
impl QueryScan {
 fn NHB_direct_word(&mut self,candidate:u32)->bool {
'''+body+'''
 false
 }
 fn NHB_direct_cursor(&mut self,block:&[u8;32],cursor:&mut usize)->(bool,u32) {
  let mut iterator=query_words(block).into_iter();
  if *cursor>0 {let _=iterator.nth(*cursor-1);}
  let candidate=iterator.next().unwrap();*cursor+=1;
  (self.NHB_direct_word(candidate),candidate)
 }
}
fn NHB_natural_member(accepted:&[u32;22],len:usize,candidate:u32)->bool {'''+member+'''}
fn NHB_scalar_ref(len:usize,draws:usize,start:usize,window:usize,old_value:u32,candidate:u32,member:bool)
 ->(bool,u32,usize,usize,usize,u32) {
 let halted=len==22 || draws==64;
 (halted,candidate,start+1,if halted || member {len}else{len+1},if halted{draws}else{draws+1},
 if !halted && !member && window==len {candidate}else{old_value})
}
#[kani::requires(len<=22 && draws<=64 && start<8 && window<22 && '''+restriction+' && '+canon+' && '+inactive+''' && old_value==accepted[window] && candidate==(u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1)) && member==NHB_natural_member(&accepted,len,candidate))]
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
'''
(E/'NHB_direct_word.rs.txt').write_text(s)
(E/'NHB_DIRECT_WORD.json').write_text(json.dumps(dict(mode=mode,source_start=src[:a].count('\n')+1,source_end=src[:b].count('\n')+1,body_sha256=hashlib.sha256(body.encode()).hexdigest(),body_exact=True,ghosts=['old_value=prestate accepted[window]','candidate=prestate block little-endian masked word','member=prestate scalar natural OR, NOT native contains result'],postcondition='six scalar observations; empty external modifies set (all actual inputs owned)',native_contains='executes actual Std .contains, never stubbed',domain='canonical22 array with inactive zero cells; len<=22; draws<=64; cursor<8; window<22; ghosts uniquely determined from those inputs'),indent=2)+'\n')
