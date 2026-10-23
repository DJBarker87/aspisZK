import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareSuccessBindMapV1

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) :=
  AspisR1S9SourceResultTransportV1.mapResult f r

/-- Bind-map transport where continuation correctness is needed only for
successful source states. This is the form used by extracted do-blocks whose
later operands are canonical only after earlier successful operations. -/
theorem mapResult_bind_congr_of_success {A A' B B' : Type}
    (f : B → B') (g : A → A') (r : Result A) (r' : Result A')
    (k : A → Result B) (k' : A' → Result B')
    (hr : mapResult g r = r')
    (hk : ∀ a b, r = .ok a → g a = b → mapResult f (k a) = k' b) :
    mapResult f (do let a ← r; k a) = (do let b ← r'; k' b) := by
  rw [← hr]
  cases r with
  | fail e => rfl
  | div => rfl
  | ok a => exact hk a (g a) rfl rfl

#print axioms mapResult_bind_congr_of_success

end AspisR1S9QMSquareSuccessBindMapV1
