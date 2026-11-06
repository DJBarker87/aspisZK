from pathlib import Path
import json
E=Path(__file__).resolve().parent;plan=[]
for idx,x in enumerate(json.loads((E/'NLC_STEP_PLAN.json').read_text())):
 name=x['site'];mod='NLC_Frame_'+name
 text='''import NLC_Step_NAME
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source input frame for every possible reply, with no successful-child premise.
This does not assert a physical native frame or a native cut producer. -/
theorem frame_NAME {H : Type} (s : State H) (atSite : s.next = .NAME) :
 AllLeaves (FramePost s) (step s) := by
 rw [step_NAME s atSite]
 unfold window_NAME
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | exact returned_frame s _ _ _
 | exact frame_put s _ _
 | exact frame_next s _
 | (change True; trivial)
 | split
#print axioms frame_NAME
#print frame_NAME
end AspisR1.NLC_Finish
end
'''.replace('NAME',name)
 (E/'NLC_generated'/(mod+'.lean')).write_text(text)
 plan.append({'module':mod,'site':name,'attempt':f'NLC_L{52+idx:03}'})
(E/'NLC_FRAME_PLAN.json').write_text(json.dumps(plan,indent=2));print('Generated32 source frame obligations')
