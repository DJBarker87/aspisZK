import Aeneas.Std
namespace PV_B3_BoundedLoop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

-- Fuel bounds recursion only. Every Result tag, including panic/divergence
-- from the body, is retained; exhaustion is unreachable under decreasing rank.
def bounded {α β : Type} (body : α → Result (ControlFlow α β)) : Nat → α → Result β
  | 0, x => match body x with
    | .ok (.done y) => .ok y
    | .ok (.cont _) => .div
    | .fail e => .fail e
    | .div => .div
  | n+1, x => match body x with
    | .ok (.done y) => .ok y
    | .ok (.cont y) => bounded body n y
    | .fail e => .fail e
    | .div => .div

theorem source_eq_bounded {α β : Type} (body : α → Result (ControlFlow α β))
    (rank : α → Nat)
    (decreases : ∀ x y, body x = .ok (.cont y) → rank y < rank x) :
    ∀ n x, rank x ≤ n → loop body x = bounded body n x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [loop.eq_def]
    cases hb : body x with
    | fail e => simp only [bounded,hb]
    | div => simp only [bounded,hb]
    | ok cf =>
      cases cf with
      | done y => simp only [bounded,hb]
      | cont y => have hd := decreases x y hb; omega
  | succ n ih =>
    intro x hx
    rw [loop.eq_def]
    cases hb : body x with
    | fail e => simp only [bounded,hb]
    | div => simp only [bounded,hb]
    | ok cf =>
      cases cf with
      | done y => simp only [bounded,hb]
      | cont y =>
        have hd := decreases x y hb
        simp only [bounded,hb]
        exact ih y (by omega)

#print axioms bounded
#print axioms source_eq_bounded
end PV_B3_BoundedLoop
