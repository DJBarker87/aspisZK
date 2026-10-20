#!/usr/bin/env python3
"""Pin the source/step syntactic bridge; this is not a Lean extraction claim."""
from pathlib import Path
import re, hashlib, json
root=Path(__file__).resolve().parents[6]
# Locate the repository without depending on the caller's working directory.
while not (root/'crates/aspis-prover/src').is_dir(): root=root.parent
rows=[]
for name,prefix,limit in [('state_only_hiding.rs','mask','MASK_SAMPLE_RETRY_LIMIT'),('state_only_entropy.rs','source','16')]:
 p=root/'crates/aspis-prover/src'/name;s=p.read_text()
 start=s.index('    fn m31(&mut self)');end=s.index('\n    fn qm31(',start)
 body=s[start:end]
 canonical=re.sub(r'\s+','',body).replace('aspis_core::field::','')
 expected='fnm31(&mutself)->Result<M31,StateOnlyMaskBuildError>{for_in0..'+limit+'{letcandidate=self.next_word()&0x7fff_ffff;ifcandidate<P{returnOk(M31(candidate));}}Err(StateOnlyMaskBuildError::MaskSampleExhausted)}'
 assert canonical==expected,(name,canonical)
 if prefix=='mask': assert 'const MASK_SAMPLE_RETRY_LIMIT: usize = 16;' in s
 hs=s.index('    fn '+prefix+'_try_step()');he=s.index('\n    #[kani::proof]',hs)
 harness=s[hs:he]
 assert 'rom::reset(2)' in harness and 'actual.next_word() & 0x7fff_ffff' in harness
 assert 'assert!(actual.word <= 8)' in harness
 assert harness.count('rom::reset(')==1
 for field in ['counter','block','word']: assert 'assert_eq!(actual.'+field+', after.'+field+')' in harness
 rows.append(dict(path=str(p.relative_to(root)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),loop_limit=16,step_harness=prefix+'_try_step',scope='exact source try expression with absorbing return normalization; Kani-to-Lean embedding remains explicit'))
print(json.dumps(rows,indent=2))
