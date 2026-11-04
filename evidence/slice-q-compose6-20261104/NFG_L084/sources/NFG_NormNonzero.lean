import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace NFG_NormNonzero
/-- Symbolic domain lemma: no concrete recurrence is evaluated. -/
theorem zero_iff {p : Nat} [Fact (Nat.Prime p)] (mod4 : p % 4 = 3) (a b : ZMod p) :
 a^2+b^2=0 ↔ a=0 ∧ b=0 := by
 constructor
 · intro sum
   by_cases hb : b=0
   · have sq : a^2=0 := by simpa [hb] using sum
     have ha : a=0 := by simpa using sq
     exact ⟨ha,hb⟩
   · have ha : a^2= -(b^2) := eq_neg_iff_add_eq_zero.mpr sum
     have impossible : (a/b)^2= -1 := by
      rw [div_pow,ha]
      simp [hb]
     exact False.elim (ZMod.mod_four_ne_three_of_sq_eq_neg_one impossible mod4)
 · rintro ⟨rfl,rfl⟩
   simp

theorem prime : Nat.Prime 2147483647 := by norm_num

theorem nonzero (a b : ZMod 2147483647) (live : ¬(a=0 ∧ b=0)) : a^2+b^2≠0 := by
 letI : Fact (Nat.Prime 2147483647) := ⟨prime⟩
 intro zero
 exact live ((zero_iff (by decide) a b).mp zero)
#print axioms zero_iff
#print axioms prime
#print axioms nonzero
end NFG_NormNonzero
