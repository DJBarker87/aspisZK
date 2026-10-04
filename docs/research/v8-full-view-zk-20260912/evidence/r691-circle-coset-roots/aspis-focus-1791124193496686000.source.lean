import AspisV8R19.R689SelectedRootExponents
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

open R689SelectedRootExponents (exponent exponent_pos exponent_lt_order
  exponent_injective exponent_sum_mod_ne_zero)

def cosetRoot (n : Fin (2^18)) : M31Exact := (g ^ exponent n).re

private theorem generator_finite : IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2^31, by norm_num, g_pow_two_pow_31⟩

private theorem norm_power (n : Nat) : QuadraticAlgebra.norm (g^n) = (1:M31Exact) := by
  rw [map_pow, g_norm_one, one_pow]

theorem cosetRoot_injective : Function.Injective cosetRoot := by
  intro i j hre
  obtain heq | hprod := same_first_coordinate (g^exponent i) (g^exponent j)
    (norm_power _) (norm_power _) hre
  · have hm := generator_finite.pow_inj_mod.mp heq
    rw [generator_order, Nat.mod_eq_of_lt (exponent_lt_order i),
      Nat.mod_eq_of_lt (exponent_lt_order j)] at hm
    exact exponent_injective hm
  · have hp : g^(exponent i+exponent j)=1 := by rw [pow_add]; exact hprod
    have hd := orderOf_dvd_iff_pow_eq_one.mpr hp
    rw [generator_order] at hd
    exact False.elim (exponent_sum_mod_ne_zero i j (Nat.mod_eq_zero_of_dvd hd))

theorem cosetRoot_ne_one (n : Fin (2^18)) : cosetRoot n ≠ 1 := by
  intro h
  obtain heq | hprod := same_first_coordinate (g^exponent n) (1:CM31Exact)
    (norm_power _) (by simp) h
  all_goals
    have hp : g^exponent n=1 := by first | exact heq | simpa only [mul_one] using hprod
    have hd := orderOf_dvd_iff_pow_eq_one.mpr hp
    rw [generator_order] at hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mod_eq_of_lt (exponent_lt_order n)] at hz
    have hpos := exponent_pos n
    omega

theorem square_first_coordinate (z : Circle (F := F))
    (hz : QuadraticAlgebra.norm z=1) : (z^2).re = 2*z.re^2-1 := by
  have hnorm : z.re*z.re+z.im*z.im=1 := by
    simpa [QuadraticAlgebra.norm_def] using hz
  simp only [pow_two, QuadraticAlgebra.re_mul]
  linear_combination -hnorm

#print axioms cosetRoot_injective
#print axioms cosetRoot_ne_one
#print axioms square_first_coordinate
end AspisV8R19.R691CircleCosetRoots
