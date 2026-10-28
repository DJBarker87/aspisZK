"""Factor generated literal storage into fixed 32-cell chunks, named length proofs.
No Rust change; validates ordered U16 values against both pinned raw emissions.
"""
from pathlib import Path
import re,json,hashlib,sys
E=Path('evidence/pv-batch2-20261027/batch2c');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
a=[]
for op in [251,253]:
 s=(E/f'batch2c-extraction-1/generated-{op}/Funs.lean').read_text();m=re.search(r'def host_weights.HOST_COEFFICIENT_TO_ROW.*?Array.make 1024#usize \[(.*?)\]',s,re.S);v=re.findall(r'\d+#u16',m[1]);assert len(v)==1024;a.append(v)
assert a[0]==a[1];v=a[0]
text='import Aeneas\nset_option autoImplicit false\nnamespace PV_B2_C_Table\nopen Aeneas Aeneas.Std\n'
for i in range(32):
 text+=f'def chunk{i} : List U16 := ['+', '.join(v[i*32:(i+1)*32])+f']\ntheorem length{i} : chunk{i}.length = 32 := by rfl\n#print axioms length{i}\n'
def tree(xs):
 if len(xs)==1:return xs[0]
 k=len(xs)//2;return '('+tree(xs[:k])+' ++ '+tree(xs[k:])+')'
text+='def values : List U16 := '+tree([f'chunk{i}' for i in range(32)])+'\n'
text+='theorem length_values : values.length = (1024#usize).val := by\n  simp only [values, List.length_append, '+', '.join(f'length{i}' for i in range(32))+']\n  rfl\n'
text+='def table : Array U16 1024#usize := Array.make 1024#usize values length_values\n#print axioms length_values\n#print axioms table\nend PV_B2_C_Table\n'
outputs={L/'PV_B2_C_Table.lean':text}
for op in [251,253]:
 p=L/f'PV_B2_C_RawWeights{op}Funs.lean';s=p.read_text()
 s=re.sub(r'(def host_weights.HOST_COEFFICIENT_TO_ROW : Array Std.U16 1024#usize :=).*?(?=\n\n/--)',r'\1\n  PV_B2_C_Table.table',s,flags=re.S)
 if 'import R1Z.PV_B2_C_Table\n' not in s:s=s.replace('import Aeneas\n','import Aeneas\nimport R1Z.PV_B2_C_Table\n',1)
 outputs[p]=s
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
r=dict(cells=1024,chunk_size=32,identical_ordered_literals_in_both_emissions=True,adaptation='flat literal → balanced append of 32 literal lists; named length lemmas; no value change',outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
p=E/'TABLE-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==r
else:p.write_text(json.dumps(r,indent=2)+'\n')
