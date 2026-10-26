import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_QuotientHead
open PV_CB3_SamplerCarry
set_option autoImplicit false

/-- Once a retained quotient is below one machine word, all higher words
contribute zero. The source may read only word zero at this point. -/
theorem high_words_zero (radix head : Nat) (tail : List Nat)
    (small : value radix (head :: tail) < radix) : value radix tail = 0 := by
  have positive : 0 < radix := by
    simp only [value] at small
    omega
  by_contra h
  have hm := Nat.mul_le_mul_left radix (Nat.one_le_iff_ne_zero.mpr h)
  simp only [Nat.mul_one] at hm
  simp only [value] at small
  omega

theorem head_value (radix head : Nat) (tail : List Nat)
    (small : value radix (head :: tail) < radix) : value radix (head :: tail) = head := by
  simp only [value, high_words_zero radix head tail small, Nat.mul_zero, Nat.add_zero]

theorem zero_digits (base : Nat) (positive : 0 < base) (digits : List Nat)
    (zero : value base digits = 0) : ∀ d, d ∈ digits → d = 0 := by
  induction digits with
  | nil => intro d h; simp only [List.not_mem_nil] at h
  | cons x xs ih =>
    have hx : x = 0 := by simp only [value] at zero; omega
    have ht : value base xs = 0 := by
      simp only [value, hx, Nat.zero_add] at zero
      exact (Nat.mul_eq_zero.mp zero).resolve_left (by omega)
    intro d hd
    rcases List.mem_cons.mp hd with h | h
    · simpa only [h] using hx
    · exact ih ht d h

#print axioms high_words_zero
#print axioms head_value
#print axioms zero_digits
end R1Z.PV_CB3_QuotientHead
