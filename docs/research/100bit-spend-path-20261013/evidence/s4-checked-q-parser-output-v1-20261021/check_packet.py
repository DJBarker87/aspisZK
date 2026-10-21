#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for name,pin in m['source_pins'].items():
 p=Path(pin['path'])
 if not p.is_absolute(): p=root/p
 if sha(p)!=pin['sha256']: raise SystemExit(f'source pin mismatch ({name}): {p}')
lean=(root/'sources/QCheckedQCurrentSemanticsV1.lean').read_text()
for token in ['[q.c0.a, q.c0.b, q.c1.a, q.c1.b]','Q.from_limbs (sourceLimbs q)','installed_parser_success_strict','checked_q_source_output_coordinates']:
 if token not in lean: raise SystemExit(f'missing Lean source marker: {token}')
rust=Path(m['source_pins']['candidate_source']['path']).read_text()
for token in ['canonical::Q::from_limbs(limbs_of(k))','[k.c0.a.0, k.c0.b.0, k.c1.a.0, k.c1.b.0]']:
 if token not in rust: raise SystemExit(f'missing frozen source expression: {token}')
print('PASS: source hashes and exact checked_q limb order')
