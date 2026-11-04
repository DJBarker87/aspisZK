import PV_B3P_DominatedEvents578227
import PV_B3P_Offset226V3
namespace PV_B3P_CountdownEvents592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
def step (count : Usize) : Usize :=
  if 0 < count.val then Usize.wrapping_sub count 1#usize else count

def counter (initial : Usize) : Nat → Usize
  | 0 => initial
  | n+1 => step (counter initial n)

theorem counter_bound (initial : Usize) (n : Nat) :
    (counter initial n).val ≤ initial.val := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    change (step (counter initial n)).val ≤ initial.val
    by_cases active : 0 < (counter initial n).val
    · simp only [step,if_pos active]
      rw [PV_B3P_Offset226V3.sub_value _ _ (by change 1 ≤ (counter initial n).val; omega)]
      change (counter initial n).val - 1 ≤ initial.val
      omega
    · simp only [step,if_neg active]
      exact ih

/-- Observation follows the source positive test and actual wrapping decrement;
failed/diverging intervening computations have no later index observation. -/
def sourceEvent (initial : Usize) (slack n : Nat) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  if 0 < (counter initial n).val then
    through effects (some ⟨(Usize.wrapping_sub (counter initial n) 1#usize).val,initial.val+slack⟩)
  else .ok none

theorem event_certificate {α : Type} (initial : Usize) (slack n : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent initial slack n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  apply (index_out_of_bounds observed normal first second).2
  by_cases active : 0 < (counter initial n).val
  · simp only [sourceEvent,if_pos active] at ran
    have frame := through_value _ _ _ ran
    cases frame
    change (Usize.wrapping_sub (counter initial n) 1#usize).val < initial.val+slack
    rw [PV_B3P_Offset226V3.sub_value _ _ (by change 1 ≤ (counter initial n).val; omega)]
    have upper := counter_bound initial n
    change (counter initial n).val - 1 < initial.val+slack
    omega
  · simp only [sourceEvent,if_neg active] at ran
    cases ran
#print axioms counter_bound
#print axioms event_certificate
end PV_B3P_CountdownEvents592227
