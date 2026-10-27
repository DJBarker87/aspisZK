import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace R1Z.PV_Inv_Norm
variable {K : Type} [Field K]

def Norm (r a b : K) : K := a^2-r*b^2

theorem norm_zero (r a b : K) (nonsquare : ∀ t : K, t^2 ≠ r)
    (hz : Norm r a b = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b=0
  · have ha : a^2=0 := by simpa [Norm,hb] using hz
    have ha0 : a = 0 := by
      rw [pow_two] at ha
      exact (mul_eq_zero.mp ha).elim id id
    exact ⟨ha0,hb⟩
  · have hr : (a/b)^2=r := by
      rw [div_pow,div_eq_iff (pow_ne_zero 2 hb)]
      exact sub_eq_zero.mp hz
    exact (nonsquare (a/b) hr).elim

theorem norm_nonzero (r a b : K) (nonsquare : ∀ t : K, t^2 ≠ r)
    (hn : a ≠ 0 ∨ b ≠ 0) : Norm r a b ≠ 0 := by
  intro hz
  obtain ⟨ha,hb⟩ := norm_zero r a b nonsquare hz
  rcases hn with h|h
  · exact h ha
  · exact h hb

#print axioms norm_zero
#print axioms norm_nonzero
end R1Z.PV_Inv_Norm
