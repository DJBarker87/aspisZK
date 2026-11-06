import NIW_AlignFinishComposed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishNewAbort
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

theorem observe_none {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) (tail : ∀ value,call=ok (.Ok value) → (next value).2.2=none) :
 (observe call event next).2.2=none := by
 cases call with
 | fail err => rfl
 | div => rfl
 | ok reply =>
  cases reply with
  | Err err => rfl
  | Ok value => exact tail value rfl

/-- NEW Err/fail/div supplies no owner and no pair detail. Earlier round
aborts also supply no pair detail. No dummy owner or successful NEW is needed. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) :
 match (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z with
 | ok (.Ok _) => True
 | _ => (run r loc v p a).2.2=none := by
 cases newCall : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z with
 | fail err =>
  unfold run
  apply observe_none
  intro first firstCall
  apply observe_none
  intro claim claimCall
  simp only [newCall,observe]
 | div =>
  unfold run
  apply observe_none
  intro first firstCall
  apply observe_none
  intro claim claimCall
  simp only [newCall,observe]
 | ok reply =>
  cases reply with
  | Err err =>
   unfold run
   apply observe_none
   intro first firstCall
   apply observe_none
   intro claim claimCall
   simp only [newCall,observe]
  | Ok owner => trivial

#print axioms observe_none
#print axioms source
end AspisR1.NIW_AlignFinishNewAbort
