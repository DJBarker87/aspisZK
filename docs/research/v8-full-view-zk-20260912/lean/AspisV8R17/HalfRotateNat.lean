import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega

/-! Focused replay of LineNorm's retained low-31 rotate argument. Definitions,
statements and the bit-case proof route are retained; closed numeral reductions
use core simplification rather than importing Mathlib.Tactic. -/
namespace AspisV8.LineNorm
def p : Nat := 2147483647
def halfWord (x : Nat) := (x >>> 1) ||| ((x &&& 1) <<< 30)

theorem half_arithmetic (x : Nat) (hx : x<p) :
    halfWord x = x/2+(x%2)*1073741824 := by
  dsimp [halfWord]
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  have hbit : x%2=0 ∨ x%2=1 := by omega
  rcases hbit with h | h
  · simp [h]
  · simp only [h, Nat.one_mul]
    apply Nat.or_two_pow_eq_add_of_lt (n:=30)
    dsimp [p] at hx
    change x/2 < 1073741824
    omega

theorem half_range_and_double (x : Nat) (hx : x<p) :
    halfWord x<p ∧ 2*halfWord x=x+(x%2)*p := by
  rw [half_arithmetic x hx]
  dsimp [p] at *
  have hm := Nat.mod_lt x (by decide : 0<2)
  have hd := Nat.mod_add_div x 2
  omega

theorem half_word_ranges (x : Nat) (hx : x<p) :
    x>>>1<2^32 ∧ (x&&&1)<<<30<2^32 ∧ halfWord x<2^32 := by
  have hh := (half_range_and_double x hx).1
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.shiftLeft_eq]
  dsimp [p] at hx hh
  have hm := Nat.mod_lt x (by decide : 0<2)
  simp only [Nat.reducePow]
  omega

theorem half_double_mod (x : Nat) (hx : x<p) :
    (2*halfWord x)%p=x := by
  rw [(half_range_and_double x hx).2, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt hx]

#print axioms half_double_mod
#print axioms half_arithmetic
#print axioms half_range_and_double
#print axioms half_word_ranges
end AspisV8.LineNorm
