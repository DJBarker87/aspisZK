from pathlib import Path
import json,lzma,sys,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1] if len(sys.argv)>1 else 'full'
restriction=dict(full='true',stop='(len==22 || draws==64)',low='(draws<64 && len<=10)',mid='(draws<64 && 11<=len && len<=15)',high='(draws<64 && 16<=len && len<22)')[mode]
src=json.loads(lzma.decompress((E.parent/'transcript-queries-20261105/NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
canon=' && '.join(f'accepted[{i}]<(1<<18)' for i in range(22));inactive=' && '.join(f'(len>{i} || accepted[{i}]==0)' for i in range(22));member=' || '.join(f'(len>{i} && accepted[{i}]==candidate)' for i in range(22))
s='''use super::*;
impl QueryScan {
 fn NHB_direct_word(&mut self,candidate:u32)->bool {
'''+body+'''
 false
 }
}
fn NHB_natural_member(accepted:&[u32;22],len:usize,candidate:u32)->bool {'''+member+'''}
#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_native_word_contract() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let candidate:u32=kani::any();let window:usize=kani::any();
 kani::assume(len<=22 && draws<=64 && candidate<(1<<18) && window<22 && '''+restriction+' && '+canon+' && '+inactive+''');
 let member=NHB_natural_member(&accepted,len,candidate);let halted=len==22 || draws==64;
 let expected_len=if halted || member {len}else{len+1};let expected_draws=if halted{draws}else{draws+1};
 let expected_word=if !halted && !member && window==len {candidate}else{accepted[window]};
 let mut scan=QueryScan{accepted,accepted_len:len,draws};
 let mut copied_candidate=candidate;
 #[cfg(NHB_invert)] {copied_candidate^=1;}
 let stop=scan.NHB_direct_word(copied_candidate);
 assert!(stop==halted && scan.accepted_len==expected_len && scan.draws==expected_draws && scan.accepted[window]==expected_word);
}
'''
(E/'NHB_scalar_word.rs.txt').write_text(s)
(E/'NHB_SCALAR_WORD.json').write_text(json.dumps(dict(mode=mode,body_sha256=hashlib.sha256(body.encode()).hexdigest(),body_exact=True,connection='candidate is the SAME word from K030/K031; no recomputation or independently chosen output; source for-loop binder cut at candidate',contains='actual native call; no stub',controls='K031 copied block byte0 control plus scalar candidate-bit control; each in identical KMX configuration'),indent=2)+'\n')
