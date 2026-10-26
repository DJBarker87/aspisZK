"""Emit the exact table with named32-cell length lemmas, avoiding a1024-cell simp."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p7'
s=(e/'coeff-table-Funs.lean.txt').read_text()
vals=[int(x) for x in re.findall(r'(\d+)#u16',s)]
assert len(vals)==1024
native=(Path(__file__).with_name('proof')/'table.rs').read_text()
a=native.index('[\n')+2;b=native.index('];',a)
assert vals==[int(x) for x in re.findall(r'\d+',native[a:b])]
out='''import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRwP7CoefficientTable
open Aeneas Aeneas.Std Result
namespace table
'''
for i in range(32):
 out+=f'def chunk{i} : List U16 := ['+','.join(f'{n}#u16' for n in vals[32*i:32*i+32])+']\n'
 out+=f'theorem chunk{i}_length : chunk{i}.length=32 := rfl\n'
out+='def values : List U16 := '+' ++ '.join(f'chunk{i}' for i in range(32))+'\n'
out+='theorem values_length : values.length=1024 := by\n  simp only [values,List.length_append,'+','.join(f'chunk{i}_length' for i in range(32))+']\n'
out+='@[irreducible] def COEFFICIENT_REFERENCE : Array U16 1024#usize := ⟨values,values_length⟩\n'
out+='def coefficient_table : Result (Array U16 1024#usize) := ok COEFFICIENT_REFERENCE\nend table\n'
out+='theorem total : table.coefficient_table=ok table.COEFFICIENT_REFERENCE := rfl\n'
for i in range(32):out+=f'#print axioms table.chunk{i}_length\n'
out+='#print axioms table.values_length\n#print axioms total\nend R1Z.ProverRwP7CoefficientTable\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP7CoefficientTable.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 (e/'coefficient-table-source-map.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Exact1024 extracted scalar values, checked against native-verified reference.32 named32-cell lists and symbolic append length proof replace rejected default Array.make length simp; no cap/depth/heartbeat increase and no recurrence reduction.'),indent=2)+'\n')
