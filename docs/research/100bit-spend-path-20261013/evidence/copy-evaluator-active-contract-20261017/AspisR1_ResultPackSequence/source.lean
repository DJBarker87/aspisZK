import Aeneas.Std

/-! Packing a successful four-tuple before its continuation, proved before
instantiating source array types and their dependent numeral evidence. -/
set_option autoImplicit false
namespace AspisR1.ResultPackSequence
open Aeneas Aeneas.Std Result

theorem bind_packed_four {A B C D E F : Type} (result : Result (A × B × C × D))
    (pack : A → B → C → D → E) (next : E → Result F) :
    (do let (a,b,c,d) ← result; next (pack a b c d)) =
      (do let e ← (do let (a,b,c,d) ← result; ok (pack a b c d)); next e) := by
  cases result with
  | fail err => rfl
  | div => rfl
  | ok tuple => rcases tuple with ⟨a,b,c,d⟩; rfl

theorem first_bind_packed_four {A B C D E F G : Type} (first : Result A)
    (rest : A → Result (B × C × D × E)) (pack : B → C → D → E → F)
    (next : F → Result G) :
    (do let a ← first; let (b,c,d,e) ← rest a; next (pack b c d e)) =
      (do let f ← (do let a ← first; let (b,c,d,e) ← rest a; ok (pack b c d e)); next f) := by
  cases first with
  | fail err => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    exact bind_packed_four (rest a) pack next

#print axioms bind_packed_four
#print axioms first_bind_packed_four
end AspisR1.ResultPackSequence
