import R1Z.PV_RunJoin_ResultTransport
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BindCongruence
open Aeneas Aeneas.Std Result

theorem bind_same {A B : Type} (m : Result A) (left right : A → Result B)
    (same : ∀ a, left a = right a) : (m >>= left) = (m >>= right) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok a => exact same a

theorem if_same {A : Type} (condition : Prop) [Decidable condition]
    (leftThen leftElse rightThen rightElse : A)
    (yes : leftThen = rightThen) (no : leftElse = rightElse) :
    (if condition then leftThen else leftElse) =
      (if condition then rightThen else rightElse) := by
  rw [yes,no]

#print axioms bind_same
#print axioms if_same
end R1Z.PV_RunJoin_BindCongruence
