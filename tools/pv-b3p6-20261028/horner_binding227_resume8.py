"""Bind the actual immutable-read transformations in the two reverse Horner loops.
Partial item(b) only: all other transformations remain explicit residuals.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';P=Path('tools/pv-b3p6-20261028/v244');source=(P/'host_terminal.rs').read_text();owned=(P/'reference_terminal.rs').read_text();token=lambda s:re.findall(r'\w+|[^\s]',s)
rows=[]
for name in ['semantic','poseidon']:
 pattern=r'while index > 0 \{\s*index -= 1;\s*composition = prepared_theta\.mul\(composition\)\.add\('+name+r'\[index\]\);\s*\}'
 m=re.search(pattern,source);assert m,name
 target=m[0].replace(name+'[index]',f'read227({name},index)')
 assert token(target)in[] if False else True
 candidate=re.search(r'while index > 0 \{\s*index -= 1;\s*composition = prepared_theta\.mul\(composition\)\.add\(read227\('+name+r',index\)\);\s*\}',owned);assert candidate,name
 assert token(candidate[0])==token(target)
 rows.append(dict(array=name,source_line=source[:m.start()].count('\n')+1,owned_line=owned[:candidate.start()].count('\n')+1,source_tokens=token(m[0]),owned_tokens=token(candidate[0]),only_change=f'{name}[index] -> read227({name},index)',body_theorem=f'horner_{name}_body_binding8',loop_theorem=f'horner_{name}_loop_binding8'))
header='''namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''
body='import PV_B3P_P227_13a\nimport PV_B3P_Success227\n'+header+'''theorem read_helper_binding8 {N : Usize} (values : Array aspis_core.field.QM31 N) (i : Usize) :
    reference_terminal.read227 values i = Array.index_usize values i := rfl

theorem digest_helper_binding8 (values : Array (Array U32 8#usize) 20#usize) (i : Usize) :
    reference_terminal.digest227 values i = Array.index_usize values i := rfl

/-- The original direct read body, with identical decrement/multiply/read/add order. -/
def horner_direct_body8 {N : Usize} (values : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    Result (ControlFlow (aspis_core.field.QM31 × Usize) aspis_core.field.QM31) := do
  if index > 0#usize then
    let next ← lift (Usize.wrapping_sub index 1#usize)
    let product ← host_terminal_field.PreparedQm31Multiplier.mul prepared composition
    let value ← Array.index_usize values next
    let sum ← aspis_core.field.QM31.add product value
    Result.ok (.cont (sum,next))
  else Result.ok (.done composition)

attribute [local irreducible] host_terminal_field.PreparedQm31Multiplier.mul
  aspis_core.field.QM31.add Array.index_usize
'''
for name,n,k in [('semantic',24,1),('poseidon',4,2)]:
 body+=f'''\ntheorem horner_{name}_body_binding8 (values : Array aspis_core.field.QM31 {n}#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop{k}.body values prepared composition index =
      horner_direct_body8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop{k}.body horner_direct_body8
  simp only [read_helper_binding8]
#print axioms horner_{name}_body_binding8
'''
body+='\n#print axioms read_helper_binding8\n#print axioms digest_helper_binding8\nend PV_B3P_Success227\n'
loops='import PV_B3P_HornerBodyBinding8227\n'+header+'''def horner_direct_loop8 {N : Usize} (values : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) : Result aspis_core.field.QM31 :=
  loop (fun state : aspis_core.field.QM31 × Usize =>
    horner_direct_body8 values prepared state.1 state.2) (composition,index)

attribute [local irreducible] horner_direct_body8
'''
for name,n,k in [('semantic',24,1),('poseidon',4,2)]:
 loops+=f'''\ntheorem horner_{name}_loop_binding8 (values : Array aspis_core.field.QM31 {n}#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop{k} values prepared composition index =
      horner_direct_loop8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop{k} horner_direct_loop8
  apply congrArg (fun body => loop body (composition,index))
  funext state
  exact horner_{name}_body_binding8 values prepared state.1 state.2
#print axioms horner_{name}_loop_binding8
'''
loops+='\nend PV_B3P_Success227\n'
files={'PV_B3P_HornerBodyBinding8227':body,'PV_B3P_HornerLoopBinding8227':loops}
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(status='partial structural binding only; not V244 closure',evidence_class='structural; chained field arithmetic',semantic_use='reclassification within existing Charon/Aeneas tool trust',source_sha256=hashlib.sha256(source.encode()).hexdigest(),owned_sha256=hashlib.sha256(owned.encode()).hexdigest(),applications=rows,claims='complete-Result equality of two actual emitted Horner bodies and loops after replacing owned read227 by original direct immutable array indexing; arbitrary arrays/prepared multiplier/accumulator/initial index, including failure/divergence',remaining='every other transformed body and complete native binding; D188 matrix and slice/pre-inline std coverage; source interpretation and compiler boundary retained',deployed_features_record='native227-composition-features.json',deployed_source_freeze='native227-composition-source-freeze.json',new_native_differential=False,prior_native_credit='finite validation only, reused unchanged; not universal proof')
if '--check'in sys.argv:assert json.loads((D/'resume8/horner-structural-partial.json').read_text())==record
else:(D/'resume8/horner-structural-partial.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(modules=list(files),source_bindings=len(rows),whole_row_closed=False)))
