import PV_B3P_DominatedEvents578227
import PV_B3P_Offset226V3
namespace PV_B3P_WindowEvents578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Both actual source comparisons are executed before subtraction/indexing.
The wrapping upper endpoint is retained even if base+width would overflow. -/
def sourceEvent (base width value : Usize) (slack : Nat) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  if base.val ≤ value.val then
    if value.val < (Usize.wrapping_add base width).val then
      through effects (some ⟨(Usize.wrapping_sub value base).val,width.val+slack⟩)
    else .ok none
  else .ok none

theorem event_guard (base width value : Usize) (slack : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent base width value slack effects = .ok (some observed)) :
    indexGuard observed := by
  by_cases lower : base.val ≤ value.val
  · by_cases upper : value.val < (Usize.wrapping_add base width).val
    · simp only [sourceEvent,if_pos lower,if_pos upper] at ran
      have frame := through_value _ _ _ ran
      cases frame
      have modbound : (Usize.wrapping_add base width).val ≤ base.val+width.val := by
        rw [Usize.wrapping_add_val_eq]
        exact Nat.mod_le _ _
      change (Usize.wrapping_sub value base).val < width.val+slack
      rw [PV_B3P_Offset226V3.sub_value value base lower]
      omega
    · simp only [sourceEvent,if_pos lower,if_neg upper] at ran
      cases ran
  · simp only [sourceEvent,if_neg lower] at ran
    cases ran

theorem event_certificate {α : Type} (base width value : Usize) (slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent base width value slack effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard base width value slack effects observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_WindowEvents578227
