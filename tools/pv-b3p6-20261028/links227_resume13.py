"""Explicit typed per-function refinement predicates; no source interpretation is
invented. The source_model argument must still be instantiated from exact-source
extraction or own-1 evidence before the predicate can earn binding credit.
"""
from pathlib import Path
import json,re
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume13'
raw=(D/'raw227-composition-resume5/Funs.lean').read_text();names=re.findall(r'^def (\S+)',raw,re.M)
rows=json.loads((D/'resume12/coverage.json').read_text())['rows'];s='''import PV_B3P_TopDown13227
namespace PV_B3P_Links13227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
noncomputable section
/-- Every source_model argument is UNINSTANTIATED until exact source association.
These predicates are not axioms, native implementations, or closure claims. -/
''';out=[]
for r in rows:
 if r['bound'] or r['inventory_status']=='identical':continue
 name=r['key'].split('#')[0];prefix=dict(terminal='reference_terminal',copy='reference_copy_terminal',field='reference_field',poseidon='reference_poseidon')[r['family']]
 matches=[n for n in names if n.startswith(prefix+'.') and n.split('.')[-1]==name]
 if not matches:
  assert r['inventory_status']=='source-only' or name=='sum_high';out.append(dict(index=r['inventory_index'],function=name,status='exact source model missing; no fabricated model equation',link=None));continue
 assert len(matches)==1,(name,matches)
 target=matches[0];link='PV_B3P_Link_'+r['family']+'_'+name
 s+=f'def {link} (source_model : _) := source_model = @{target}\n#print {link}\n\n'
 out.append(dict(index=r['inventory_index'],function=name,link='PV_B3P_Links13227.'+link,target='PV_B3P_227.'+target,status='predicate defined; exact source_model not instantiated; NOT discharged'))
s+='''/-- Ordered list adapter for the exact source range-slice traversal. -/
def sum_ranges_reference13 (high : Array aspis_core.field.QM31 64#usize) :
    List (Usize × Usize) → aspis_core.field.QM31 → Result aspis_core.field.QM31
  | [], sum => .ok sum
  | (start, finish)::ranges, sum => do
      let next ← reference_terminal.sum_interval227 high sum start finish
      sum_ranges_reference13 high ranges next
def PV_B3P_Link_terminal_sum_high
    (source_model : reference_copy_terminal.Selectors → List (Usize × Usize) → Result aspis_core.field.QM31) : Prop :=
  ∀ selectors ranges, source_model selectors ranges =
    sum_ranges_reference13 selectors.high ranges aspis_core.field.QM31.ZERO
#print PV_B3P_Link_terminal_sum_high

/-- Source-only Poseidon expand, after an explicit checked slice adapter. -/
def PV_B3P_Link_poseidon_expand
    (source_model : (N : Usize) → Array aspis_core.field.QM31 10#usize → Usize → Usize → Result (Array aspis_core.field.QM31 N)) : Prop :=
  source_model = reference_copy_terminal.Selectors.expand

/-- Source-only selector constructor; the adapter must retain all bounds/error paths. -/
def selector_reference13 (point : Array aspis_core.field.QM31 10#usize) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let selectors ← reference_copy_terminal.Selectors.at_point point
  reference_terminal.poseidon_selectors selectors

def PV_B3P_Link_poseidon_at_point
    (source_model : Array aspis_core.field.QM31 10#usize → Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) : Prop :=
  source_model = selector_reference13
#print PV_B3P_Link_poseidon_expand
#print PV_B3P_Link_poseidon_at_point
end
end PV_B3P_Links13227
'''
for r in out:
 if r['link'] is None:r['link']='PV_B3P_Links13227.PV_B3P_Link_'+('terminal_'if r['function']=='sum_high'else 'poseidon_')+r['function'];r['status']='predicate defined for checked source adapter; exact adapter/model missing; NOT discharged'
(L/'PV_B3P_LinkDefinitions13227.lean').write_text(s);(O/'link-status.json').write_text(json.dumps(out,indent=2)+'\n')
