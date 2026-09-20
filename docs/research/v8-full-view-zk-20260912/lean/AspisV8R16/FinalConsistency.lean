import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The mandatory raw quotient / Final256 consistency relation.
This is a fold identity, not a full-view coverage or soundness theorem. -/
set_option autoImplicit false
namespace AspisV8R16
variable {F : Type*} [Field F]

/-- Same normalized two-butterfly formula as the selected source fold. -/
def foldFour (x y alpha v0 v1 v2 v3 : F) : F :=
  let positive := (v0+v1)/2 + alpha*(v0-v1)/(2*y)
  let negative := (v2+v3)/2 - alpha*(v2-v3)/(2*y)
  (positive+negative)/2 + alpha^2*(positive-negative)/(2*x)

theorem fold_channels (x y alpha a b c d : F)
    (h2 : (2 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    foldFour x y alpha
      (a+b*y+c*x+d*x*y) (a-b*y+c*x-d*x*y)
      (a-b*y-c*x+d*x*y) (a+b*y-c*x-d*x*y) =
      a+alpha*b+alpha^2*c+alpha^3*d := by
  dsimp [foldFour]
  field_simp
  ring

/-- If raw quotient changes are zero, their folded value cannot be an
independent target. Apply at each queried fibre. -/
theorem zero_raw_forces_zero_final (x y alpha a b c d : F)
    (h2 : (2 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h0 : a+b*y+c*x+d*x*y=0) (h1 : a-b*y+c*x-d*x*y=0)
    (h2v : a-b*y-c*x+d*x*y=0) (h3 : a+b*y-c*x-d*x*y=0) :
    a+alpha*b+alpha^2*c+alpha^3*d=0 := by
  rw [← fold_channels x y alpha a b c d h2 hx hy, h0, h1, h2v, h3]
  simp [foldFour]

#print axioms fold_channels
#print axioms zero_raw_forces_zero_final
end AspisV8R16
