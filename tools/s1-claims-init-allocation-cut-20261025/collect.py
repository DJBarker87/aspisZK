#!/usr/bin/env python3
"""Seal source-only failed diagnostics; no build or proof launch."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-claims-init-allocation-cut-20261025';P.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=[R/'tools/s1-claims-init-allocation-cut-20261025']+[E/f's1-claims-init-allocation-cut-v{n}'for n in range(1,7)]
files={}
for root in roots:
 for p in root.rglob('*'):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.o','.rlib','.rmeta','.out','.goto','.llbc','.pyc']
   files[str(p.relative_to(R))]=sha(p)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
 status='FAILED_DIAGNOSTICS_ONLY',accepted_proofs=[],freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a',
 files=files,print_axioms='N/A: no Lean result',
 next_action='No unchanged allocation/cap retry or identical pointer-cast substitution. Native initialization requires a supported semantics/tool route or a separately approved/equivalent source candidate. Whole SDK/allocator/error/effect/artifact joins remain.'),indent=2)+'\n')
print(json.dumps(dict(status='FAILED_DIAGNOSTICS_SEALED',files=len(files))))
