import PV_B3P_InclusiveFormatting569227
import PV_B3P_DominatedEvents578227
namespace PV_B3P_InclusiveEvents592227
open Aeneas Aeneas.Std core.ops.range PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false

/-- The loop's private upper endpoint is preserved on every source next,
including exhausted and singleton branches. -/
theorem next_end (handler : Str → Result Never) (r next : RangeInclusive Usize)
    (item : Option Usize)
    (ran : PV_B3P_InclusiveFormatting569227.source handler r = .ok (item,next)) :
    next.end = r.end := by
  by_cases empty : r.exhausted = true ∨ r.end.val < r.start.val
  · simp only [PV_B3P_InclusiveFormatting569227.source,if_pos empty] at ran
    cases ran
    rfl
  · by_cases active : r.start.val < r.end.val
    · simp only [PV_B3P_InclusiveFormatting569227.source,if_neg empty,if_pos active,
        PV_B3P_NthFormattingFinal559227.increment_value handler r.start r.end active,bind_tc_ok] at ran
      cases ran
      rfl
    · simp only [PV_B3P_InclusiveFormatting569227.source,if_neg empty,if_neg active] at ran
      cases ran
      rfl

def sourceEvent (handler : Str → Result Never) (r : RangeInclusive Usize)
    (slack : Nat) (effects : List (Result Unit)) : Result (Option IndexState) := do
  let (item,_) ← PV_B3P_InclusiveFormatting569227.source handler r
  match item with
  | none => .ok none
  | some i => through effects (some ⟨i.val,r.end.val+1+slack⟩)

theorem event_certificate {α : Type} (handler : Str → Result Never) (r : RangeInclusive Usize)
    (slack : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler r slack effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  apply (index_out_of_bounds observed normal first second).2
  by_cases empty : r.exhausted = true ∨ r.end.val < r.start.val
  · simp only [sourceEvent,PV_B3P_InclusiveFormatting569227.source,if_pos empty,bind_tc_ok] at ran
    cases ran
  · have upper : r.start.val ≤ r.end.val := by omega
    by_cases active : r.start.val < r.end.val
    · simp only [sourceEvent,PV_B3P_InclusiveFormatting569227.source,if_neg empty,if_pos active,
        PV_B3P_NthFormattingFinal559227.increment_value handler r.start r.end active,bind_tc_ok] at ran
      have frame := through_value _ _ _ ran
      cases frame
      change r.start.val < r.end.val+1+slack
      omega
    · simp only [sourceEvent,PV_B3P_InclusiveFormatting569227.source,if_neg empty,if_neg active,bind_tc_ok] at ran
      have frame := through_value _ _ _ ran
      cases frame
      change r.start.val < r.end.val+1+slack
      omega
#print axioms next_end
#print axioms event_certificate
end PV_B3P_InclusiveEvents592227
