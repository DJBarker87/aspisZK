"""Typed conjunction of all unchanged per-function links, with an explicit
joint model-instance witness. No claim that these model slots are native code."""
from pathlib import Path
import json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';rows=json.loads((D/'resume13/link-status.json').read_text())
s='''import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Groups13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227
set_option autoImplicit false
universe u
abbrev Slot13 {α : Sort u} (_target : α) := α
noncomputable section
structure ChangedBodies13 where
'''
for i,r in enumerate(rows):
 target=r.get('target','').removeprefix('PV_B3P_227.')
 if not target:
  target=dict(sum_high='(fun (selectors : reference_copy_terminal.Selectors) ranges => sum_ranges_reference13 selectors.high ranges aspis_core.field.QM31.ZERO)',expand='reference_copy_terminal.Selectors.expand',at_point='selector_reference13')[r['function']]
 r['group_slot']='body'+str(i);r['group_target']=target
 s+='  '+r['group_slot']+' : Slot13 (@'+target+')\n'if not target.startswith('(')else '  '+r['group_slot']+' : Slot13 '+target+'\n'
s+='\ndef PV_B3P_Link_changed_bodies (source : ChangedBodies13) : Prop :=\n  '+' ∧\n  '.join(r['link'].removeprefix('PV_B3P_Links13227.')+' source.'+r['group_slot']for r in rows)+'\n'
s+='\ndef explicit_model_bodies13 : ChangedBodies13 where\n'
for r in rows:s+='  '+r['group_slot']+' := '+('(@'+r['group_target']+')'if not r['group_target'].startswith('(')else r['group_target'])+'\n'
s+='''
/-- Joint satisfiability of the typed 36-function group, for a concrete MODEL
instance. It does not instantiate the actual deployed source interpretation. -/
theorem changed_bodies_satisfiable13 :
    PV_B3P_Link_changed_bodies explicit_model_bodies13 := by
  repeat' constructor
  all_goals
    repeat' intro
    rfl
#print axioms changed_bodies_satisfiable13
end
end PV_B3P_Groups13227
''';(L/'PV_B3P_LinkGroup13227.lean').write_text(s);(D/'resume13/link-group-slots.json').write_text(json.dumps(rows,indent=2)+'\n')
