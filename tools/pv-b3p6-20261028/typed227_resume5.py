"""Expose the already determined scalar/array types of the long prepared sum.
This changes binder annotations only. A source-erasure check is mandatory.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-lifted-resume5.lean.txt';s=p.read_text();a=s.index('/-- [pv_b3p6_reference227::reference_field::qm31_sum_products3_prepared]');b=s.index('\n/-- [',a+1);old=s[a:b];annotations=[]
def f(m):
 name=m[1];kind=m[2]
 ty=('Std.U64' if re.fullmatch(r'i\d*',name) else 'aspis_core.field.M31' if re.fullmatch(r'm\d*',name) else 'aspis_core.field.QM31' if re.fullmatch(r'q\d*',name) else 'aspis_core.field.CM31' if re.fullmatch(r'right_sum\d*',name) else 'reference_field.PreparedQm31Multiplier' if re.fullmatch(r'pqm\d*',name) else 'Array (Array Std.U64 3#usize) 3#usize' if re.fullmatch(r'sums\d*',name) else None)
 if ty is None:return m[0]
 annotations.append((name,ty));return '  let '+name+' : '+ty+' '+kind
new=re.sub(r'^  let (\w+) (←|:=)',f,old,flags=re.M)
erased=new
for n,t in annotations:erased=erased.replace('let '+n+' : '+t+' ','let '+n+' ')
assert erased==old
q=D/'ported227-typed-resume5.lean.txt';q.write_text(s[:a]+new+s[b:])
(D/'typed227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),annotations=annotations,annotation_erasure_equals_input=True,reason='42050 isDefEq heartbeat limit at long scalar binder; constrain already-fixed result types without changing any operation or raising the limit'),indent=2)+'\n')
print(len(annotations))
