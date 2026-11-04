import PV_B3P_RangeEvents578227
namespace PV_B3P_MinRangeEvents587227
open Aeneas Aeneas.Std core.ops.range PV_B3P_PanicPatterns571227
open PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Deployed Ord::min for Usize: no destructor effect, comparison is scalar. -/
def sourceMin (left right : Usize) : Usize :=
  if right.val < left.val then right else left

theorem sourceMin_le_right (left right : Usize) :
    (sourceMin left right).val ≤ right.val := by
  by_cases smaller : right.val < left.val
  · simp only [sourceMin,if_pos smaller]
    exact Nat.le_refl _
  · simp only [sourceMin,if_neg smaller]
    omega

/-- The range end is the actual min result. Candidate may wrap; no bound on
candidate or on the step-by counter is assumed or needed for this projection. -/
def sourceEvent (handler : Str → Result Never) (start candidate cap : Usize)
    (slack : Nat) (effects : List (Result Unit)) : Result (Option IndexState) := do
  let (item,_) ← PV_B3P_NextFormatting569227.source handler ⟨start,sourceMin candidate cap⟩
  match item with
  | none => .ok none
  | some i => through effects (some ⟨i.val,cap.val+slack⟩)

theorem event_guard (handler : Str → Result Never) (start candidate cap : Usize)
    (slack : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler start candidate cap slack effects = .ok (some observed)) :
    indexGuard observed := by
  by_cases active : start.val < (sourceMin candidate cap).val
  · simp only [sourceEvent,PV_B3P_NextFormatting569227.source,if_pos active,
      PV_B3P_NthFormattingFinal559227.increment_value handler start (sourceMin candidate cap) active,
      bind_tc_ok] at ran
    have frame := through_value _ _ _ ran
    cases frame
    have capped := sourceMin_le_right candidate cap
    change start.val < cap.val+slack
    omega
  · simp only [sourceEvent,PV_B3P_NextFormatting569227.source,if_neg active,bind_tc_ok] at ran
    cases ran

theorem event_certificate {α : Type} (handler : Str → Result Never) (start candidate cap : Usize)
    (slack : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler start candidate cap slack effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2
    (event_guard handler start candidate cap slack effects observed ran)
#print axioms sourceMin_le_right
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_MinRangeEvents587227
