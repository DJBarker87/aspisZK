import R1DualPad
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! The two-pad correction inhabits the base field for every challenge outside
that field in a rootless quadratic extension. This proves the algebraic
repair; legal mask spaces, transcript distributions and efficient simulation
are not modeled here. -/

set_option autoImplicit false
namespace AspisR1.DualPadQuadratic

open AspisR1.DualPad
variable {K : Type*} [Field K] {nu : K}
  [Fact (∀ r : K, r ^ 2 ≠ nu + 0 * r)]

abbrev Ext (K : Type*) [Field K] (nu : K) := QuadraticAlgebra K nu 0

/-- Determinant of a nonzero multiplier and its product with the challenge. -/
theorem determinant_eq_norm (g gamma : Ext K nu) :
    det g.re g.im (g * gamma).re (g * gamma).im =
      gamma.im * QuadraticAlgebra.norm g := by
  simp only [det, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.norm_def]
  ring

theorem determinant_ne_zero (g gamma : Ext K nu)
    (hg : g ≠ 0) (hgamma : gamma.im ≠ 0) :
    det g.re g.im (g * gamma).re (g * gamma).im ≠ 0 := by
  rw [determinant_eq_norm]
  exact mul_ne_zero hgamma
    (fun h => hg (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h))

/-- The concrete exponents of the existing G and D pad lanes. -/
theorem pad_determinant_ne_zero (gamma : Ext K nu) (hgamma : gamma.im ≠ 0) :
    det (gamma ^ 27).re (gamma ^ 27).im
      (gamma ^ 28).re (gamma ^ 28).im ≠ 0 := by
  have hg : gamma ≠ 0 := by
    intro h
    apply hgamma
    simpa [h]
  simpa only [show 28 = 27 + 1 from rfl, pow_succ] using
    determinant_ne_zero (gamma ^ 27) gamma (pow_ne_zero 27 hg) hgamma

/-- Both repair coefficients are in K and their embedded combination cancels
any extension-field coefficient c. -/
theorem correction (g d c : Ext K nu)
    (hdet : det g.re g.im d.re d.im ≠ 0) :
    c + g * algebraMap K (Ext K nu) (u g.re g.im d.re d.im c.re c.im) +
      d * algebraMap K (Ext K nu) (v g.re g.im d.re d.im c.re c.im) = 0 := by
  apply QuadraticAlgebra.ext
  · simpa using corrected_first_equation g.re g.im d.re d.im c.re c.im hdet
  · simpa using corrected_second_equation g.re g.im d.re d.im c.re c.im hdet

theorem pad_correction (gamma : Ext K nu) (hgamma : gamma.im ≠ 0) (lane : Nat) :
    gamma ^ lane +
      gamma ^ 27 * algebraMap K (Ext K nu)
        (u (gamma ^ 27).re (gamma ^ 27).im (gamma ^ 28).re (gamma ^ 28).im
          (gamma ^ lane).re (gamma ^ lane).im) +
      gamma ^ 28 * algebraMap K (Ext K nu)
        (v (gamma ^ 27).re (gamma ^ 27).im (gamma ^ 28).re (gamma ^ 28).im
          (gamma ^ lane).re (gamma ^ lane).im) = 0 :=
  correction (gamma ^ 27) (gamma ^ 28) (gamma ^ lane)
    (pad_determinant_ne_zero gamma hgamma)

#print axioms determinant_eq_norm
#print axioms determinant_ne_zero
#print axioms pad_determinant_ne_zero
#print axioms correction
#print axioms pad_correction

end AspisR1.DualPadQuadratic
