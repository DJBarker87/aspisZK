"""Factor one frozen QueryScan loop iteration, preserving native statements."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;src=json.loads(lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('            if self.accepted_len == QUERY_COUNT');b=src.index('\n        }\n        false',a);body=src[a:b]
# self is the exact same &mut QueryScan receiver; the loop's candidate is input.
s='''impl QueryScan {
 fn NGQ_word_step(&mut self,candidate:u32)->bool {
'''+body+'''
 false
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_word_step() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();let x:u32=kani::any();
 let j:usize=kani::any();kani::assume(len<=22 && draws<=64 && j<22);
 let member=accepted[..len].contains(&x);
 let mut s=QueryScan{accepted,accepted_len:len,draws};
 let stop=s.NGQ_word_step(x);let halted=len==22 || draws==64;
 let expected_len=if halted || member {len} else {len+1};
 let expected_draws=if halted {draws} else {draws+1};
 let expected_word=if !halted && !member && j==len {x} else {accepted[j]};
 let correct=stop==halted && s.accepted_len==expected_len && s.draws==expected_draws && s.accepted[j]==expected_word;
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(!correct);
}
'''
(E/'NGQ_scan_step.rs.txt').write_text(s);(E/'NGQ_SCAN_CUT.json').write_text(json.dumps(dict(start=a,end=b,sha256=hashlib.sha256(body.encode()).hexdigest()),indent=1)+'\n')
p=E/'NGQ_core_harness.rs.txt';t=p.read_text();t=t.split('// NGQ generated one-word cut')[0];p.write_text(t+'// NGQ generated one-word cut\n'+s)
