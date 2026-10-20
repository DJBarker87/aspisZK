#!/usr/bin/env python3
"""Audit the exact unchanged field source reused at six external declarations."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[5]
area=root/'docs/research/100bit-spend-path-20261013';tool=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(tool/'extract-wide-arithmetic.py'),'--check'],check=True)
current=area/'evidence/current-qm31-arithmetic-20261015/extraction/attempt-a/input/src/field.rs'
selected=tool/'wide-arithmetic-input/field.rs'
assert current.read_bytes()==selected.read_bytes(),'opaque arithmetic source changed'
for f in ['Types.lean','Funs.lean']:
 assert (area/'lean/AspisR1WideArithmetic'/f).read_bytes()==(tool/'wide-arithmetic-generated'/f).read_bytes(),f
print(json.dumps(dict(field_source_identical=True,field_sha256=hashlib.sha256(selected.read_bytes()).hexdigest(),opaque_declarations=['M31.add','M31.mul','CM31.add','CM31.mul','QM31.add','QM31.mul'],carrier_transport='coordinate copies; no extra computational law',raw_emission_unchanged=True)))
