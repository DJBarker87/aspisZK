import PV_B3P_DominatedEvents578227
namespace PV_B3P_FourWayEvents587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
def sourceCondition (observed : IndexState) : Bool :=
  decide (observed.index = 0 ∨ observed.index = 1 ∨ observed.index = 2 ∨ observed.index = 3)
theorem event_guard (column : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_DominatedEvents578227.sourceEvent 4 0 column effects = .ok (some observed)) :
    sourceCondition observed = true := by
  by_cases active : column < 4
  · simp only [PV_B3P_DominatedEvents578227.sourceEvent,if_pos active] at ran
    have frame := PV_B3P_InitializerEvents578227.through_value _ _ _ ran
    cases frame
    change decide (column = 0 ∨ column = 1 ∨ column = 2 ∨ column = 3) = true
    apply decide_eq_true
    omega
  · simp only [PV_B3P_DominatedEvents578227.sourceEvent,if_neg active] at ran
    cases ran

theorem event_certificate {α : Type} (column : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_DominatedEvents578227.sourceEvent 4 0 column effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (sourceCondition observed = true) ∧
      branch (sourceCondition observed = true) normal first = branch (sourceCondition observed = true) normal second :=
  (explicit_panic (sourceCondition observed) normal first second).2
    (event_guard column effects observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_FourWayEvents587227
