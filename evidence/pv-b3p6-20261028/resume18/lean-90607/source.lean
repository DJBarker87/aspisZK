import PV_B3P_PanicPatterns571227
namespace PV_B3P_ResultSource572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact input shape Result<Infallible,E>; E remains arbitrary. -/
def discriminant {E : Type} : core.result.Result Empty E → Nat
  | .Ok _ => 0
  | .Err _ => 1

def sourceCondition {E : Type} (r : core.result.Result Empty E) : Bool :=
  discriminant r == 1

theorem source_guard {E : Type} (r : core.result.Result Empty E) :
    sourceCondition r = true := by
  cases r with
  | Ok impossible => exact Empty.elim impossible
  | Err _ => rfl

/-- Both actual specializations use the same source input carrier shape. -/
theorem family_certificate {E α : Type} (_site : Fin 2)
    (r : core.result.Result Empty E) (normal first second : Result α) :
    ¬ diagnostic (sourceCondition r = true) ∧
      branch (sourceCondition r = true) normal first =
        branch (sourceCondition r = true) normal second :=
  (assertion (sourceCondition r) true normal first second).2 (source_guard r)
#print axioms source_guard
#print axioms family_certificate
end PV_B3P_ResultSource572227
