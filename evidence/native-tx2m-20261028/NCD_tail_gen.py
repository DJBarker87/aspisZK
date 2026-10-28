from NCD_generate import *
import json
p='crates/aspis-r1-cost-probe/src/transcript.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);start=s.index('        self.state=state;');stop=s.index('        Ok(q)',start)+len('        Ok(q)');tail=s[start:stop]
assert tail.count('crate::trace::value(5,')==22
(E/'NCD_TAIL_SOURCE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',fragment=tail,source_factor='only the reached local child Result is an input; no whole parent result'),indent=2)+'\n')
t='''
#[cfg(kani)] mod NCD_query_tail {
use super::*;
use aspis_core::transcript::QuerySampleError;
#[derive(Clone,Copy)] struct NeverDigest;
impl Digest32 for NeverDigest{fn digest(&self,_parts:&[&[u8]])->[u8;32]{assert!(false,"tail must not hash");[0;32]}}
impl Transcript<NeverDigest>{fn observed_tail(&mut self,result:Result<([u32;22],[u8;32]),QuerySampleError>)->Result<[u32;22],crate::verifier::Error>{
 let (q,state)=result.map_err(|_|crate::verifier::Error::Transcript)?;
'''+tail+'''
}}
fn rejected()->QuerySampleError{let variant:u8=kani::any();kani::assume(variant<3);match variant{
 0=>QuerySampleError::BoundNotPowerOfTwo{bound:kani::any()},
 1=>QuerySampleError::CountExceedsBound{count:kani::any(),bound:kani::any()},
 _=>QuerySampleError::DrawLimitExhausted{accepted:kani::any(),max_draws:kani::any()}
}}
'''
for claim in ['success_values','success_state','reject_state','reject_error']:
 t+='#[kani::proof] #[kani::unwind(1024)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let before:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let queries:[u32;22]=kani::any();let j:usize=kani::any();kani::assume(j<32);let i:usize=kani::any();kani::assume(i<22);
 let mut t=Transcript{state:before,hash:NeverDigest};
'''
 if claim.startswith('success'):t+='let out=t.observed_tail(Ok((queries,reply))).unwrap();\n'
 else:t+='let out=t.observed_tail(Err(rejected()));\n'
 t+=dict(success_values='assert!(out[i]==queries[i]);',success_state='assert!(t.state[j]==reply[j]);',reject_state='assert!(matches!(out,Err(crate::verifier::Error::Transcript))&&t.state[j]==before[j]);',reject_error='assert!(matches!(out,Err(crate::verifier::Error::Transcript)));')[claim]+'\n}\n'
t+='}\n';emit(p,t,'NCD_tail')
