#!/usr/bin/env python3
"""Check exact production cuts and exact retained emitted bodies, without replay."""
from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'extraction-input/source-pins.json').read_text());lib=(D/'extraction-input/lib.rs').read_bytes()
for name,h in pins['kit_files'].items():assert sha((D/'extraction-input'/name).read_bytes())==h,name
for c in pins['cuts']:
 raw=subprocess.check_output(['git','-C',str(R),'show',pins['revision']+':'+c['path']])
 body=raw[c['start_byte']:c['end_byte_exclusive']]
 assert sha(raw)==c['file_sha256'] and sha(body)==c['sha256']
 assert body in lib,c['anchor']
raw=(D/'diagnostics/raw-generated/AspisR1CurrentWideMul/Funs.lean').read_text();typ=(D/'diagnostics/raw-generated/AspisR1CurrentWideMul/Types.lean').read_text();model=(D/'sources/CurrentWideMulCanonical.lean').read_text()
a=raw.index('/-- [aspis_r1_current_wide_mul::field::');b=raw.rindex('end AspisR1CurrentWideMul');body=raw[a:b]
a=typ.index('structure field.wide_exact.WideExact');b=typ.index('\nend AspisR1CurrentWideMul',a);carrier=typ[a:b]
assert model.count(body)==1 and model.count(carrier)==1
assert 'FunsExternal' not in model and 'axiom ' not in model and 'set_option maxHeartbeats' not in model
assert 'fail panic' not in raw
for local,retained in [('field.QM31.add','field.QM31.add'),('field.QM31.mul','field.QM31.mul'),('field.cm.CM31.sub','field.CM31.sub'),('field.mul_by_r','field.mul_by_r')]:
 assert f'abbrev {local} := AspisR1Qm31ArithmeticProbe.{retained}' in model
field=R/'crates/aspis-core/src/field.rs'
retained=R/'docs/research/100bit-spend-path-20261013/evidence/current-qm31-arithmetic-20261015/extraction/attempt-a/input/src/field.rs'
assert field.read_bytes()==retained.read_bytes()
print(json.dumps({'status':'PASS','production_cuts':len(pins['cuts']),'baseline':pins['revision'],'retained_emitted_body_sha256':sha(body.encode()),'field_rs_current_equals_retained_sha256':sha(field.read_bytes()),'scope':'Exact emitted WideExact::mul/mul_u/QM31::sub retained under explicit canonical QM/CM child aliases; unchanged field.rs identity; not whole-runtime or whole soundness.'},indent=2))
