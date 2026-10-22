#!/usr/bin/env python3
import hashlib, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[5]  # repository root from evidence packet
HERE=Path(__file__).resolve().parent
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def check(p,h,label):
    path=Path(p) if str(p).startswith('/') else ROOT/p
    if not path.is_file(): raise SystemExit(f"missing {label}: {path}")
    got=digest(path)
    if got != h: raise SystemExit(f"hash mismatch {label}: {path}: {got} != {h}")
    return path
m=json.loads((HERE/'manifest.json').read_text())
if m.get('schema')!='source-correspondence-evidence-v1': raise SystemExit('bad schema')
for x in m['six_source_pins']: check(x['path'],x['sha256'],'source pin')
ident=json.loads((ROOT/'lean-candidates/s9-helper-actual-field-types-cut-v1-20261022/attempt7/source-identities.json').read_text())
field=ROOT/'crates/aspis-core/src/field.rs'
if digest(field)!=ident['opaque_arithmetic_bodies']['QM31.mul']['source_file_sha256']: raise SystemExit('current field.rs is not the pinned source')
snapshot=ROOT/'lean-candidates/s9-helper-actual-field-types-cut-v1-20261022/attempt7/source-snapshots/field.rs'
if digest(snapshot)!=digest(field): raise SystemExit('source snapshot mismatch')
for name in ('QM31.mul','QM31.square'):
    d=ident['opaque_arithmetic_bodies'][name]
    if hashlib.sha256(d['method_text'].encode()).hexdigest()!=d['method_body_sha256']: raise SystemExit(f"bad recorded method text digest: {name}")
    if d['method_text'] not in field.read_text(): raise SystemExit(f"method text not found in current source: {name}")
    if m['methods'][name]['body_sha256']!=d['method_body_sha256']: raise SystemExit(f"manifest method digest mismatch: {name}")
for x in m['lean_source_files']+m['generated_lean_files']+m['extraction_artifacts']:
    check(x['path'],x['sha256'],'pinned artifact')
translation_specs = [
    ('docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/extraction/generated/translation.json',
     'AspisR1CurrentWide.field.QM31.mul', 935, 945),
    ('docs/research/100bit-spend-path-20261013/evidence/terminal-v4-current-soundness-packet-20261019/supporting/generated-current-v4/translation.json',
     'AspisR1SelectedMaskProbe.field.QM31.square', 951, 960),
]
for rel, lean_name, lo, hi in translation_specs:
    translation = json.loads((ROOT/rel).read_text())
    rows = [f for f in translation['functions'] if f.get('lean_name') == lean_name]
    if len(rows) != 1: raise SystemExit(f"expected one translation row for {lean_name}")
    row=rows[0]
    if row.get('is_opaque') is not False: raise SystemExit(f"{lean_name} is opaque in selected extraction")
    src=row.get('source',{})
    if (src.get('begin_line'),src.get('end_line')) != (lo,hi): raise SystemExit(f"wrong source span for {lean_name}: {src}")
for x in m['owner_objects_external_refs']: check(x['path'],x['sha256'],'Lean owner object')
print(f"PASS: {len(m['six_source_pins'])} source pins, 2 method-body pins, {len(m['lean_source_files'])} Lean source pins, {len(m['generated_lean_files'])} generated source pins, {len(m['owner_objects_external_refs'])} external Lean objects")
