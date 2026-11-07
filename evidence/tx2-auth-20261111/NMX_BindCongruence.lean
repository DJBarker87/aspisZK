import NMX_ResultSteps
set_option autoImplicit false
namespace NMX_BindCongruence
open Aeneas Aeneas.Std
/-- One opaque result at a time. No child outcome is fixed to a success arm. -/
theorem step {A B : Type} (r : Result A) (left right : A → Result B)
 (same : ∀ a, left a = right a) : (r >>= left) = (r >>= right) :=
 congrArg (fun next => r >>= next) (funext same)
#print axioms step
end NMX_BindCongruence
