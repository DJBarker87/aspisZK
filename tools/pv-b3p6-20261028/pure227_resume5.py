"""Normalize only `let x <- lift pure` to the corresponding pure let.
The Aeneas library defines lift x := Result.ok x; the generic complete-Result
identity is PV_B3P_PureBind227.lift_bind. Raw extraction remains untouched.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-typed-resume5.lean.txt';s=p.read_text();a=s.index('/-- [pv_b3p6_reference227::reference_field::qm31_sum_products3_prepared]');b=s.index('\n/-- [',a+1);old=s[a:b];edits=[]
def f(m):
 edits.append(dict(before=m[0],after=m[1]+':= '+m[2]));return m[1]+':= '+m[2]
new=re.sub(r'(^  let [^\n←]+)← lift (\([^\n]*\))$',f,old,flags=re.M)
assert len(edits)>100,len(edits)
restored=new
for e in reversed(edits):
 assert restored.count(e['after'])==1,e
 restored=restored.replace(e['after'],e['before'])
assert restored==old
q=D/'ported227-pure-resume5.lean.txt';q.write_text(s[:a]+new+s[b:]);(D/'pure227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),edits=edits,roundtrip_equals_input=True,law='PV_B3P_PureBind227.lift_bind',scope='prepared3 helper only; pure binds only; all effectful binds retained; no order changes'),indent=2)+'\n');print(len(edits))
