#!/usr/bin/env python3
"""Read-only source/evidence integrity gate; never replays unchanged jobs."""
from pathlib import Path
import hashlib, json
R = Path(__file__).resolve().parents[2]
P = R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-init-local-20261025'
m = json.loads((P/'manifest.json').read_text())
for rel, digest in m['files'].items():
    assert hashlib.sha256((R/rel).read_bytes()).hexdigest() == digest, rel
d = json.loads((P/'results.json').read_text())
rows = {r['attempt']:r for r in d['attempts']}
assert rows['s1-init-local-compile-v14']['result'] == 'KANI_LAYOUT_ICE'
assert rows['s1-init-local-compile-v17']['result'] == 'COMPILED_ONLY'
assert rows['s1-init-local-compile-v25']['result'] == 'KANI_FORMATTING_POINTER_ICE'
assert rows['s1-init-local-compile-v26']['result'] == 'COMPILED_ONLY'
assert rows['s1-init-local-compile-v27']['result'] == 'KANI_UNSUPPORTED_UNION_FAILURE'
assert rows['s1-init-local-compile-v28']['result'] == 'COMPILED_ONLY'
assert rows['s1-init-local-compile-v29']['compiler_launched'] is False
assert rows['s1-init-local-compile-v30']['result'] == 'KANI_UNSUPPORTED_NICHE_FAILURE'
# Original native row-write source retained literally in the changed harness.
E = P.parent
new = (E/'s1-init-local-compile-v28/source/min/src/claims_write_proofs_scalar.rs').read_text()
old = (P/'original-min/src/claims_write_proofs.rs').read_text()
def step(s): return s[s.index('fn native_step('):s.index('fn owned_step(')]
assert step(new) == step(old)
frozen = (P/'frozen-r1_semantic.rs').read_text()
compact = lambda s: ''.join(s.split())
body='out.as_mut_ptr().cast::<[QM31;29]>().add(p).write(record.decode_k::<29>(p*29)?);'
assert body in compact(frozen) and body in compact(step(new))
assert 'aspis_core::r0::heap::uninit::<Claims>()' in new
assert 'row(kani::any())' not in new
assert 'framed.get(..length)' in new
print(f"PASS {len(m['files'])} source/evidence hashes; native row fragment unchanged; compiler readiness only, no S1/S6 closure")
