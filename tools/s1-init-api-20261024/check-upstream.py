#!/usr/bin/env python3
"""Source comparison only; neither version is executed by this audit."""
from pathlib import Path
import hashlib,json,difflib
R=Path(__file__).resolve().parents[2];P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-init-api-assessment-20261024'
m=json.loads((P/'upstream-068-layout-comparison.json').read_text());old=(P/'sources'/m['path']).read_bytes();new=(P/'upstream-068-ty-layout.rs').read_bytes();assert hashlib.sha256(new).hexdigest()==m['sha256'] and len(new)==m['bytes']
assert (old==new)==m['byte_identical_to_inspected_067']
def branch(b):
 a=b.index(b'FieldsShape::Primitive =>');z=b.index(b'FieldsShape::Array',a);return b[a:z]
assert branch(old)==branch(new) and b'FieldsShape::Primitive with a different ABI than ValueAbi::Scalar' in branch(new)
expected=''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),fromfile='Kani0.67/ty_layout.rs',tofile='Kani0.68/ty_layout.rs',n=0));assert (P/'upstream-068-layout.diff').read_text()==expected
print(json.dumps(dict(status='PASS',kind='upstream-source-comparison-only',layout_file_identical=False,failing_primitive_branch_identical=True,native_type_identified=False,native_initializedness_proved=False,compiler_or_solver_launched=False)))
