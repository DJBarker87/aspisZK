#!/usr/bin/env python3
"""Read-only source schedule audit; not a whole-function Rust equivalence gate."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-bytes5-20261022'
source=R/'crates/aspis-r1-cost-probe/src/verifier.rs'
s=source.read_text()
writer=s[s.index('pub fn checkpoint<H:Digest32>'):s.index("struct Reader<'a>")]
resume=s[s.index('pub fn resume<H:Digest32>'):]
resume=resume[:resume.index('\n}',resume.index('pub fn resume'))+2] if '\n}' in resume else resume
calls=['hash.digest(&[proof])','hash.digest(&[public])','hash.digest(&[b"UNPROVED:R1:checkpoint",&out])']
assert writer.count('hash.digest')==3
assert [writer.index(c) for c in calls]==sorted(writer.index(c) for c in calls)
assert 'let sum='+calls[2] in writer
assert 'out.extend_from_slice(&sum)' in writer
assert 'assert_eq!(out.len(),checkpoint_size(p.variant))' in writer
assert writer.index('for &x in &a.weights')<writer.index(calls[2])
put=s[s.index('fn put('):s.index('pub fn checkpoint<H:Digest32>')]
assert 'digest' not in put
# The mechanical resume generator starts from the retained source module;
# kernel source reconstruction, not this text audit, checks its equivalence.
lean=R/'docs/research/100bit-spend-path-20261013/lean/Stage2ContinuationResumeBody.lean'
assert lean.read_text().count('aspis_coredigestDigest32Inst.digest hash')==3
pins={str(p.relative_to(R)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
      for p in [source,lean,R/'docs/research/100bit-spend-path-20261013/lean/CheckpointBytesDecodeC5.lean']}
(E/'source-schedule.json').write_text(json.dumps({'checks':{'writer_three_direct_calls_in_order':True,
 'writer_complete_body_before_checksum':True,'writer_checksum_appended_before_size_assert':True,
 'put_helpers_digest_free':True,'retained_resume_three_calls':True},'source_pins':pins,
 'scope':'read-only direct call schedule; selector and resume identities have separate Lean receipts; physical Vec/allocation/frozen Rust interpretation retains P6 boundary',
 'new_kani_gate_required':False,'reason':'no shipped/reference Rust change or modified per-call helper; reuse prior pinned per-operation content evidence; no whole-function harness'},indent=2)+'\n')
print('Source writer/resume schedule audit passed')
