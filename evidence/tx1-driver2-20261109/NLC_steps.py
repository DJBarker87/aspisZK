from pathlib import Path
import re,json,textwrap
E=Path(__file__).resolve().parent
src=(E/'NLC_generated/NLC_FinishStep.lean').read_text()
body=src[src.index(' match s.next with\n')+len(' match s.next with\n'):src.index('\nend AspisR1.NLC_Finish')]
blocks=re.split(r'^ \| \.(\w+) =>[ \n]',body,flags=re.M)
plan=[]
for n in range(1,len(blocks),2):
 name=blocks[n];text=blocks[n+1].split('\n | .lowIndex | .highIndex')[0].rstrip()
 mod='NLC_Step_'+name
 code='''import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_NAME {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
BODY
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_NAME {H : Type} (s : State H) (atSite : s.next = .NAME) :
 step s = window_NAME s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_NAME
#print step_NAME
end AspisR1.NLC_Finish
end
'''.replace('NAME',name).replace('BODY','\n'.join(' '+line for line in textwrap.dedent(text).splitlines()))
 (E/'NLC_generated'/(mod+'.lean')).write_text(code)
 plan.append({'module':mod,'site':name,'attempt':f'NLC_L{20+len(plan):03}'})
(E/'NLC_STEP_PLAN.json').write_text(json.dumps(plan,indent=2));print(f'{len(plan)} source windows generated')
