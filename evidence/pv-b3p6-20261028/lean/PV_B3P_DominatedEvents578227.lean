import PV_B3P_InitializerEvents578227
namespace PV_B3P_DominatedEvents578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
open PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Overapproximation of a source event dominated by a strict scalar test.
The effects are the arbitrary intervening prefix, cut before the index call.
The source checker must bind the index to the tested private scalar snapshot.
No guard hypothesis is used to construct the observed states. -/
def sourceEvent (limit slack index : Nat) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  if index < limit then through effects (some ⟨index,limit+slack⟩) else .ok none

theorem event_guard (limit slack index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent limit slack index effects = .ok (some observed)) :
    indexGuard observed := by
  by_cases active : index < limit
  · simp only [sourceEvent,if_pos active] at ran
    have frame := through_value _ _ _ ran
    cases frame
    change index < limit + slack
    omega
  · simp only [sourceEvent,if_neg active] at ran
    cases ran

theorem event_certificate {α : Type} (limit slack index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent limit slack index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard limit slack index effects observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_DominatedEvents578227
