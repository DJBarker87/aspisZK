"""Project the exact pure269 constructor from the frozen emission, read-only."""
from pathlib import Path
import subprocess,json,lzma,hashlib,sys
L=Path(__file__).resolve().parent;R=L.parents[2]
# Reuse the retained hash-cons reader; do not regenerate session12 outputs.
s=(L/'session12_kinds.py').read_text();exec(s[:s.index('kinds={}')])
f=expand(x['fun_decls'][269]);stmts=f['body']['Structured']['body']['statements']
kinds={}
for z in stmts:
 if z['id'] in [10000,10002,10003]:
  kinds[str(z['id'])]=z['kind']['Assign'][1]['Aggregate'][0]
assert set(kinds)=={'10000','10002','10003'}
assert kinds['10000']['Adt'][1]==0 and kinds['10002']['Adt'][1]==0
assert next(z for z in stmts if z['id']==10003)['kind']['Assign'][1]['Aggregate'][1][-1]['Const']['kind']['Literal']['Bool'] is False
src='''import PV_LIB_SPEC_Success13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Builder269
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
'''
for name,key in [('nameKind','10000'),('sizeKind','10002'),('builderKind','10003')]:src+='def '+name+' : Data := '+data(kinds[key])+'\n'
src+='''/-- Exact269 source10000/10002/10003: None name, None size, no_hooks=false.
The false flag is important: the ORIGINAL default Builder DOES invoke454.
This is a source-value binding, not proof that454 has been executed. -/
def value : Data := PV_THR2_KeyValues.pack builderKind
  [PV_THR2_KeyValues.pack nameKind [],PV_THR2_KeyValues.pack sizeKind [],.boolean false]
def reply (w : OWNER) (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  match r.answer with
  | .returned (.ok _) => ⟨.returned (.ok value),w,r.events⟩
  | _ => {r with world := w}

theorem fields (p : Parameters) :
    (runtime p).carrier.field value 0 = some (PV_THR2_KeyValues.pack nameKind []) ∧
    (runtime p).carrier.field value 1 = some (PV_THR2_KeyValues.pack sizeKind []) ∧
    (runtime p).carrier.field value 2 = some (.boolean false) := ⟨rfl,rfl,rfl⟩
theorem absent (p : Parameters) :
    (runtime p).control.variant (PV_THR2_KeyValues.pack nameKind []) = some 0 ∧
    (runtime p).control.variant (PV_THR2_KeyValues.pack sizeKind []) = some 0 := ⟨rfl,rfl⟩
theorem frame (w : OWNER) (r : Reply OWNER Event Data) :
    (reply w r).world = w ∧ (reply w r).events = r.events := by
  rcases r with ⟨answer,after,events⟩
  cases answer with
  | pending => exact ⟨rfl,rfl⟩
  | fault f => exact ⟨rfl,rfl⟩
  | returned result => cases result <;> exact ⟨rfl,rfl⟩
'''
for name in ['nameKind','sizeKind','builderKind','value','reply','fields','absent','frame']:src+='#print axioms '+name+'\n'
src+='end PV_LIB_SPEC_Builder269\n'
report={'revision':rev,'source':path,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'function':269,'assignments':kinds,'no_hooks':False,'original_entry_reachability_proved':False,'hook454_bound':False}
for p,text in [(R/'lean/PV_LIB_SPEC_Builder269.lean',src),(L/'SESSION13_BUILDER_SOURCE.json',json.dumps(report,indent=2)+'\n')]:
 if '--check' in sys.argv:assert p.read_text()==text
 else:p.write_text(text)
print('PASS exact269 source constructor; default no_hooks=false')
