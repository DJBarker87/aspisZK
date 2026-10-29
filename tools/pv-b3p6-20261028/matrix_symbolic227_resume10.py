"""Named bounds laws and exact accumulator source-to-pure-storage binding.
The four field Result calls remain opaque and in their original order.
"""
from pathlib import Path
import re,json,sys,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={}
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
for i in range(3):
 s='import PV_B3P_ArrayWrite227\n'+header+f'''
def get3_{i} {{α : Type}} (xs : Array α 3#usize) : α :=
  xs.val[{i}]'(by have h:=xs.property; change xs.val.length=3 at h; omega)

theorem index3_{i} {{α : Type}} (xs : Array α 3#usize) :
    Array.index_usize xs {i}#usize = .ok (get3_{i} xs) :=
  PV_B3P_SelectIndex227.index_value xs {i}#usize (by change {i}<3; omega)

theorem borrow3_{i} {{α : Type}} (xs : Array α 3#usize) :
    Array.index_mut_usize xs {i}#usize = .ok (get3_{i} xs,Array.set xs {i}#usize) :=
  PV_B3P_ArrayWrite227.borrow xs {i}#usize (by change {i}<3; omega)

theorem update3_{i} {{α : Type}} (xs : Array α 3#usize) (value : α) :
    Array.update xs {i}#usize value = .ok (Array.set xs {i}#usize value) :=
  PV_B3P_ArrayWrite227.update xs {i}#usize (by change {i}<3; omega)
#print axioms index3_{i}
#print axioms borrow3_{i}
#print axioms update3_{i}
end PV_B3P_Binding10227
''';files[f'PV_B3P_Index3_10{i}227']=s
raw=(L/'PV_B3P_P227_00.lean').read_text();decl=raw[raw.index('def reference_field.accumulate_prepared227'):raw.index('\n\n\nend ')];body=decl.split(':= do\n',1)[1]
# Parse one monadic statement at a time, preserving all pure declarations verbatim.
chunks=re.split(r'(?=^  let |^  ok )',body,flags=re.M);chunks=[c.rstrip()for c in chunks if c.strip()]
converted=[];proof=[];rows=[];monadic=0
for c in chunks:
 if not c.startswith('  let ')or' ←'not in c:
  converted.append(c);continue
 lhs,rhs=c.split(' ←',1);rhs=rhs.strip();lhs=lhs.strip()[4:]
 if monadic<4:
  converted.append(c);proof+=['  apply bind_equal9',f'  intro {lhs}'];monadic+=1;continue
 if rhs.startswith('lift '):
  expr=rhs[5:];converted.append(f'  let {lhs} := {expr}');proof.append(f'  apply lift_head_equal9 {expr}');kind='lift'
 else:
  m=re.fullmatch(r'Array\.(index_usize|index_mut_usize|update)\s+([\s\S]*?)\s+([012])#usize(?:\s+([\s\S]*))?',rhs);assert m,(lhs,rhs)
  op,x,i,val=m.groups();x=x.strip();val=val.strip()if val else None
  if op=='index_usize':expr=f'get3_{i} {x}';law=f'index3_{i}';kind='read'
  elif op=='index_mut_usize':expr=f'(get3_{i} {x},Array.set {x} {i}#usize)';law=f'borrow3_{i}';kind='borrow'
  else:expr=f'Array.set {x} {i}#usize {val}';law=f'update3_{i}';kind='store'
  converted.append(f'  let {lhs} := {expr}');proof +=[f'  rw [{law}]','  apply equal_ok_head9']
 rows.append(dict(binding=lhs,kind=kind,source=rhs,model=expr))
params='''(sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier)'''
s='import PV_B3P_P227_00\nimport PV_B3P_LiftHeadEq9227\n'+''.join(f'import PV_B3P_Index3_10{i}227\n'for i in range(3))+header
s+=f'\ndef accumulate_pure_storage10 {params} : Result (Array (Array U64 3#usize) 3#usize) := do\n'+'\n'.join(converted)+'\n'
s+='\nattribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add UScalar.cast U64.wrapping_add U64.wrapping_mul Array.set '+ ' '.join(f'get3_{i}'for i in range(3))+'\n'
s+=f'''\ntheorem accumulate_storage_binding10 {params} :
    reference_field.accumulate_prepared227 sums right left = accumulate_pure_storage10 sums right left := by
  unfold reference_field.accumulate_prepared227 accumulate_pure_storage10
'''+ '\n'.join(proof)+'\n  rfl\n\n#print axioms accumulate_storage_binding10\nend PV_B3P_Binding10227\n'
files['PV_B3P_MatrixStorage10227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(source_module='PV_B3P_P227_00',source_sha256=hashlib.sha256(raw.encode()).hexdigest(),modules=list(files),statements=rows,field_calls_unchanged=4,credit='complete emitted accumulator array storage Result binding; source loop and final matrix model law remain separate',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'matrix-storage-binding.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(modules=list(files),statements=len(rows))))
