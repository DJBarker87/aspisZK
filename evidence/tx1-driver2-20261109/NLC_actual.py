from pathlib import Path
import json
E=Path(__file__).resolve().parent;rows=json.loads((E/'NLC_STEP_PLAN.json').read_text())
s='\n'.join('import NLC_Frame_'+x['site'] for x in rows)+'''
import NLC_Ready
import NLC_LeafSound
import NLC_Progress
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run erase)
'''
for label,predicate,assumption,lemma in [('source_input_frame','InputFrame s after','','frame'),('source_ready_next','Ready after','(before : Ready s)','ready')]:
 s+=f'''\ntheorem {label} {{H : Type}} (s after : State H) {assumption}
 (returned : (run (step s)).2 = ok (.inr after)) : {predicate} := by
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next with
'''
 for x in rows:
  name=x['site'];p='FramePost s' if lemma=='frame' else 'ReadyPost';a='' if lemma=='frame' else ' before'
  s+=f' | {name} => exact all_erase (step s) ({p}) ({lemma}_{name} s atSite{a}) (.inr after) actual\n'
 for name in ['lowIndex','highIndex']:
  s+=f''' | {name} =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
'''
 s+=f'#print axioms {label}\n'
s+='''
def FinalPost {H : Type} : Post H → Prop
 | .inl _ => True
 | .inr _ => False

theorem verified_final {H : Type} (s : State H) (atSite : s.next = .verified) :
 AllLeaves FinalPost (step s) := by
 rw [step_verified s atSite]
 unfold window_verified
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)

def Major {H : Type} (s : State H) : Prop := rank s.next < 32

theorem source_major_next {H : Type} (s after : State H) (before : Major s)
 (returned : (run (step s)).2 = ok (.inr after)) : Major after := by
 have order := source_progress s after returned
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next
 all_goals first
 | exact False.elim (all_erase (step s) FinalPost (verified_final s atSite) (.inr after) actual)
 | (unfold Major at *;simp only [atSite,rank] at *;omega)

#print axioms verified_final
#print axioms source_major_next
end AspisR1.NLC_Finish
end
'''
(E/'NLC_generated/NLC_SourceActual.lean').write_text(s)
