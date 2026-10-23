from pathlib import Path
import json
R=Path(__file__).resolve().parent
gen=R/'evidence/aeneas/generated'
meta=json.loads((gen/'translation.json').read_text())
functions=meta['functions']; assert functions and meta['types']
expected={'QM31.square':('src/field.rs',951),'WideExact.mul_qm31':('src/field/wide_exact.rs',178)}
found={}
for f in functions:
 src=f.get('source') or {}
 for label,(path,line) in expected.items():
  if src.get('file')==path and src.get('begin_line')==line:
   assert f['is_opaque'] is False,(label,f)
   found[label]=f
assert set(found)==set(expected)
lean=(gen/'AspisR1S9SquareMulQMCutV1/Funs.lean').read_text()
for label,f in found.items():
 relative=f['lean_name'].removeprefix('AspisR1S9SquareMulQMCutV1.')
 assert f'def {relative}' in lean,(label,relative)
field=[f for f in functions if (f.get('source') or {}).get('file') in ('src/field.rs','src/field/wide_exact.rs')]
assert len(field)==17 and all(not f['is_opaque'] for f in field)
assert any(f['lean_name'].endswith('focused_qm31_square') for f in functions)
assert any(f['lean_name'].endswith('focused_wide_exact_mul_qm31') for f in functions)
print('Aeneas output: 2 requested targets concrete, 17 generated field callees concrete, harnesses present')
