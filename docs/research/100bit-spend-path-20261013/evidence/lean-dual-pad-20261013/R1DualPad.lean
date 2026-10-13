import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact two-equation field algebra for the dual-pad correction.

This proves only the displayed algebraic identities. In particular it makes no
claim about privacy, the choice of a field extension, or any protocol use. -/

set_option autoImplicit false

namespace AspisR1.DualPad

variable {K : Type*} [Field K]

def det (g0 g1 d0 d1 : K) : K := g0 * d1 - g1 * d0

def u (g0 g1 d0 d1 c0 c1 : K) : K :=
  (c1 * d0 - c0 * d1) / det g0 g1 d0 d1

def v (g0 g1 d0 d1 c0 c1 : K) : K :=
  (g1 * c0 - g0 * c1) / det g0 g1 d0 d1

theorem corrected_first_equation (g0 g1 d0 d1 c0 c1 : K)
    (hdet : det g0 g1 d0 d1 ≠ 0) :
    c0 + g0 * u g0 g1 d0 d1 c0 c1 +
      d0 * v g0 g1 d0 d1 c0 c1 = 0 := by
  unfold u v
  field_simp [det, hdet]
  simp only [det]
  ring

theorem corrected_second_equation (g0 g1 d0 d1 c0 c1 : K)
    (hdet : det g0 g1 d0 d1 ≠ 0) :
    c1 + g1 * u g0 g1 d0 d1 c0 c1 +
      d1 * v g0 g1 d0 d1 c0 c1 = 0 := by
  unfold u v
  field_simp [det, hdet]
  simp only [det]
  ring

theorem determinant_expansion (g0 g1 a b nu : K) :
    det g0 g1 (g0 * a + nu * g1 * b) (g0 * b + g1 * a) =
      b * (g0 ^ 2 - nu * g1 ^ 2) := by
  dsimp [det]
  ring

#print axioms corrected_first_equation
#print axioms corrected_second_equation
#print axioms determinant_expansion

end AspisR1.DualPad
