#!/usr/bin/env python3
"""Retain source pins and exact nonce ownership excerpts; no source mutation."""
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
ranges={
 'docs/research/v8-r0-zk-20261009/LOG.md':[(39,44),(5154,5158),(8006,8016)],
 'docs/research/v8-full-view-zk-20260912/HONEST_PROVER_EXPERIMENT.md':[(15,27)],
 'docs/research/v8-full-view-zk-20260912/PUBLIC_VIEW.md':[(18,25)],
 'crates/aspis-prover/src/state_only_entropy.rs':[(172,224),(392,447),(901,956)],
 'crates/aspis-r1-cost-probe/src/prover.rs':[(100,135),(168,177),(325,376)],
}
checks={
 'crates/aspis-prover/src/state_only_entropy.rs':[
  'pub fn generate_for_mask_nonce(\n        mask_nonce: [u8; 32],',
  'let mut bytes = Zeroizing::new([0u8; 64]);',
  'if mask_nonce == [0; 32]',
  'hasher.update(mask_nonce);',
  'Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false)'],
 'crates/aspis-r1-cost-probe/src/prover.rs':[
  'mut next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>',
  'let attempt=next_attempt(k)?;',
  'a client that binds the nonce to the proof-account address',
 ]}
# Source spelling in comments is pinned too; matching is case-insensitive only
# for the human prose marker, not the Rust clauses.
records=[]
for name,spans in ranges.items():
 p=Path(name);data=p.read_bytes();source=data.decode();lines=source.splitlines()
 for needle in checks.get(name,[]):
  assert needle in source or (needle=='clients' and needle in source.lower()),needle
 records.append(dict(path=name,sha256=hashlib.sha256(data).hexdigest(),size=len(data),
  excerpts=[dict(start_line=a,end_line=b,text='\n'.join(lines[a-1:b])) for a,b in spans]))
(E/'nonce-source-audit.json').write_text(json.dumps(dict(
 revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 method='Read-only source inspection with exact retained excerpts; not a Rust executable test or source refinement theorem.',
 sources=records,
 finding='The preselected-nonce API samples 64 private seed bytes and does not sample, constrain the origin of, or establish independence/uniformity of its caller-supplied nonzero nonce.',
 safe_wrapper='prove_masked_retrying fixes next_attempt to StateOnlyAttemptSecrets::generate; the generic callback API does not.',
 ),indent=2)+'\n')
print('Nonce source excerpts and hashes retained.')
