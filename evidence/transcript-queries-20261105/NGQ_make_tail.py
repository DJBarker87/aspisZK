"""Pin the callee-boundary tail and preserve all 22 evaluated arguments."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;src=json.loads(lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-r1-cost-probe/src/transcript.rs']
a=src.index('        let (q,state)=aspis_core::r0_transcript::queries_from_pairs');b=src.index('\n    }',a);original=src[a:b];callee='aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances)';assert original.count(callee)==1
body=original.replace(callee,'reply')
s='''use super::*;
#[derive(Clone,Copy)] struct NGQ_NoDigest;
impl aspis_core::Digest32 for NGQ_NoDigest {
 fn digest(&self,_:&[&[u8]])->[u8;32] {panic!("unexpected digest in tail")}
}
impl<H:aspis_core::Digest32> Transcript<H> {
 fn NGQ_tail(&mut self,reply:Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>)->Result<[u32;22],crate::verifier::Error> {
'''+body+'''
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_tail() {
 let old:[u8;32]=kani::any();let q:[u32;22]=kani::any();let selected:[u8;32]=kani::any();
 let good:bool=kani::any();let tag:u8=kani::any();kani::assume(tag<3);
 let error=match tag {
  0=>aspis_core::transcript::QuerySampleError::BoundNotPowerOfTwo{bound:kani::any()},
  1=>aspis_core::transcript::QuerySampleError::CountExceedsBound{count:kani::any(),bound:kani::any()},
  _=>aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:kani::any(),max_draws:kani::any()},
 };
 let reply=if good {Ok((q,selected))}else{Err(error)};
 let j:usize=kani::any();let i:usize=kani::any();kani::assume(j<32 && i<22);
 let mut t=Transcript{state:old,hash:NGQ_NoDigest};
 let out=t.NGQ_tail(reply);
 let correct=match out {
  Ok(result)=>good && result[i]==q[i] && t.state[j]==selected[j],
  Err(crate::verifier::Error::Transcript)=>!good && t.state[j]==old[j],
  _=>false,
 };
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(!correct);
}
'''
(E/'NGQ_tail_harness.rs.txt').write_text(s);(E/'NGQ_TAIL_CUT.json').write_text(json.dumps(dict(start=a,end=b,source_sha256=hashlib.sha256(original.encode()).hexdigest(),substitution=callee+' -> reply',cut_sha256=hashlib.sha256(body.encode()).hexdigest(),trace_arguments=22),indent=1)+'\n')
