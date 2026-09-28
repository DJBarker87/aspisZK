import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace R24NativeBounds

-- Small symbolic leaves only; no source-refinement or privacy claim.
theorem raw32_product_bound (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    a * b < 2^64 := by
  calc
    a*b ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
    _ < 2^64 := by norm_num

def P : Nat := 2147483647

theorem canonical_product_bound (a b : Nat) (ha : a < P) (hb : b < P) :
    a*b ≤ (P-1)^2 := by
  calc
    a*b ≤ (P-1)*(P-1) := Nat.mul_le_mul (by omega) (by omega)
    _ = (P-1)^2 := by ring

-- These bounds dominate every pre-reduction accumulator in the guarded kernel.
theorem accumulator_constants :
    2*P^2+3*P < 2^64 ∧
    2*(P-1)^2+3*(P-1) < 2^64 ∧
    2*(P-1)^2+2*P^2 < 2^64 ∧
    4*(P-1)^2 < 2^64 ∧
    (P-1)^2 < P^2 := by norm_num [P]

variable {F : Type*} [CommRing F]
def cm (a b c d : F) : F × F := (a*c-b*d, a*d+b*c)

theorem schoolbook_tower (a b c d e f g h : F) :
    let m0 := cm a b e f
    let m1 := cm c d g h
    let m2 := cm (a+c) (b+d) (e+g) (f+h)
    (m0.1 + (2*m1.1-m1.2), m0.2 + (m1.1+2*m1.2),
      m2.1-m0.1-m1.1, m2.2-m0.2-m1.2) =
    (a*e-b*f+2*(c*g-d*h)-(c*h+d*g),
      a*f+b*e+(c*g-d*h)+2*(c*h+d*g),
      a*g+c*e-b*h-d*f, a*h+b*g+c*f+d*e) := by
  dsimp [cm]
  ext <;> ring

#print axioms raw32_product_bound
#print axioms canonical_product_bound
#print axioms accumulator_constants
#print axioms schoolbook_tower
end R24NativeBounds
