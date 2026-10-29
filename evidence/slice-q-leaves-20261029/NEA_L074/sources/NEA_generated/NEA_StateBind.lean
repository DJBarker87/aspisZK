import NEA_StateLaws
set_option autoImplicit false
namespace NEA_StateBind
open Aeneas Aeneas.Std Result
/-- Rewrite the complete continuation, without higher-order matching through a pair pattern. -/
theorem bind_pair {A B : Type} (r : Result A) (k : A × Unit → Result B) :
    (NEA_StateLaws.lift r >>= k) = (r >>= fun x => k (x,())) := by
  cases r <;> rfl
#print axioms bind_pair
end NEA_StateBind
