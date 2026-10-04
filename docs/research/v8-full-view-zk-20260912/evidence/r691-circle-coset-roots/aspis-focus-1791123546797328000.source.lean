import AspisV8R19.R690CircleGeneratorCertificate
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R691CircleCosetRoots
variable {F : Type*} [Field F]
abbrev Circle := QuadraticAlgebra F (-1) 0

/-- The only two norm-one circle points with a fixed first coordinate are
identical or multiplicative inverses. This is field algebra, not source execution. -/
theorem same_first_coordinate (z w : Circle (F := F))
    (hz : QuadraticAlgebra.norm z = 1)
    (hw : QuadraticAlgebra.norm w = 1) (hre : z.re = w.re) :
    z = w ∨ z * w = 1 := by
  have hz' : z.re*z.re + z.im*z.im = 1 := by
    simpa [QuadraticAlgebra.norm_def] using hz
  have hw' : w.re*w.re + w.im*w.im = 1 := by
    simpa [QuadraticAlgebra.norm_def] using hw
  have hprod : (z.im-w.im)*(z.im+w.im)=0 := by
    rw [hre] at hz'
    linear_combination hz' - hw'
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact QuadraticAlgebra.ext hre (sub_eq_zero.mp h)
  · right
    have him : z.im = -w.im := eq_neg_of_add_eq_zero_left h
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one]
      rw [hre,him]
      linear_combination hw'
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_one]
      rw [hre,him]
      ring
#print axioms same_first_coordinate

open AspisV8R15.ExactTowerBase
open R690CircleGeneratorCertificate

theorem generator_order : orderOf g = 2^31 := by
  have hnot : ¬g^(2^30)=1 := by
    rw [g_pow_two_pow_30]
    intro h
    have hre := congrArg QuadraticAlgebra.re h
    change (-1 : M31Exact) = 1 at hre
    have hc : ((-1 : ℤ) : M31Exact) = ((1 : ℤ) : M31Exact) := by
      simpa only [Int.cast_neg, Int.cast_one] using hre
    have hmod := (ZMod.intCast_eq_intCast_iff (-1) 1 P).mp hc
    norm_num [Int.ModEq, P] at hmod
  exact orderOf_eq_prime_pow (p := 2) (n := 30) hnot g_pow_two_pow_31

#print axioms generator_order
end AspisV8R19.R691CircleCosetRoots
