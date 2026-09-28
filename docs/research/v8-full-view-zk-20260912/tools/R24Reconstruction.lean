import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace R24Reconstruction
variable {F : Type*} [CommRing F]

theorem flattened (a b c d e f g h i : F) :
    let x0 := a-b
    let y0 := c-a-b
    let x1 := d-e
    let y1 := f-d-e
    let x2 := g-h
    let y2 := i-g-h
    (x0+2*x1-y1, y0+x1+2*y1, x2-x0-x1, y2-y0-y1) =
    (a+3*d-b-e-f, c+2*f-a-b-d-3*e,
      g+b+e-h-a-d, i+a+b+d+e-g-h-c-f) := by
  dsimp
  ext <;> ring

theorem bounds :
    10*(2147483647:Nat) < 2^35 ∧
    3*(2147483647-1:Nat) < 3*2147483647 ∧
    4*(2147483647-1:Nat) < 4*2147483647 ∧
    6*(2147483647-1:Nat) < 6*2147483647 := by norm_num

#print axioms flattened
#print axioms bounds
end R24Reconstruction
