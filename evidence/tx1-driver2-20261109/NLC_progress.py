from pathlib import Path
import json
E=Path(__file__).resolve().parent;rows=json.loads((E/'NLC_STEP_PLAN.json').read_text())
s='''import NLC_Rank
import NLC_LeafSound
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run erase)
/-- The progress fact is derived from actual source execution, rather than
supplied as a source endpoint or child-success premise. -/
theorem source_progress {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) :
 rank after.next = rank s.next + 1 := by
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next with
'''
for x in rows:
 name=x['site'];s+=f''' | {name} => simpa only [RankPost,atSite] using all_erase (step s) (RankPost s) (rank_{name} s atSite) (.inr after) actual\n'''
for name in ['lowIndex','highIndex']:
 s+=f''' | {name} =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
'''
s+='''
def fuel {H : Type} (s : State H) : Nat := 34 - rank s.next

theorem fuel_positive {H : Type} (s : State H) : 0 < fuel s := by
 have := rank_bound s.next
 unfold fuel
 omega

theorem fuel_next {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) : fuel s = fuel after + 1 := by
 have order := source_progress s after returned
 have beforeBound := rank_bound s.next
 have afterBound := rank_bound after.next
 unfold fuel
 omega
#print axioms source_progress
#print axioms fuel_positive
#print axioms fuel_next
end AspisR1.NLC_Finish
end
'''
(E/'NLC_generated/NLC_Progress.lean').write_text(s)
