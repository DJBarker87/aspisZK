import PV_B3P_PositiveRangeEvents587227
namespace PV_B3P_PositiveRange587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_PositiveRangeEvents587227
set_option autoImplicit false
/-- Actual old private Range1..16 counter, captured for source508:31208. -/
theorem certificate {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate n effects observed ran normal first second
#print axioms certificate
end PV_B3P_PositiveRange587227
