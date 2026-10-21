#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s7-kani3-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def item(s,marker,start=0):
 a=s.index(marker,start);b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
field=subprocess.check_output(['git','show','b2727acd3:crates/aspis-core/src/field.rs'],text=True)
wide=subprocess.check_output(['git','show','b2727acd3:crates/aspis-core/src/field/wide_exact.rs'],text=True)
assert Path(R/'crates/aspis-core/src/field.rs').read_text()==field
assert Path(R/'crates/aspis-core/src/field/wide_exact.rs').read_text()==wide
items=[]
for marker,port in [('fn canonical_qm31','S7Kani3CanonicalBackend.canonicalQM'),('pub fn sub(self','S7Kani3WideBackend.subWide'),('pub fn mul(self','S7Kani3WideBackend.mulWide'),('pub fn mul_qm31(self','S7Kani3CanonicalBackend.mulMixed'),('fn mul_u','S7Kani3WideBackend.mulU')]:
 t=item(wide,marker);items.append(dict(rust=t,sha256=sha(t.encode()),lean_port=port))
t=item(field,'pub fn sub(self',field.index('impl QM31'))
items.append(dict(rust=t,sha256=sha(t.encode()),lean_port='S7Kani3WideBackend.qmSub'))
(E/'backend-bindings.json').write_text(json.dumps(dict(frozen_revision='b2727acd3',field_sha256=sha(field.encode()),wide_sha256=sha(wide.encode()),items=items,scope='Explicit additive ports of production feature-off arithmetic. Canonical carriers and ordered field-call dependencies are proved. Full ABI/extracted-cone/observer and SBF correspondence are separate P6 boundaries.',changes=['private Wide coordinates represented by existing two-QM31 record','QM31.sub port added because inherited extraction omitted that method','canonical_qm31 closure flattened in coordinate order','mulWide evaluates independent sx/sy sums before cross and mul_u; operand order and each dependent operation retained','instrumentation/reference-only cfg branches excluded as in inherited selected extraction']),indent=2)+'\n')
print('Frozen arithmetic bodies pinned; explicit port ledger recorded')
