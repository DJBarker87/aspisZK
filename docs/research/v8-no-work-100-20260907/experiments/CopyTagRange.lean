import Mathlib.Tactic
namespace AspisV8.CopyTagRange
def p : Nat := 2147483647
def tagMax : Nat := 1124073607
def word : Nat := 2^64

theorem raw_product_bound (a t : Nat) (ha : a < p) (ht : t ≤ tagMax) :
    a*t ≤ (p-1)*tagMax := Nat.mul_le_mul (by omega) ht

theorem sum_le_length (xs : List Nat) (bound : Nat) (hx : ∀ x ∈ xs, x ≤ bound) :
    xs.sum ≤ xs.length*bound := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := hx a (by simp)
    have hi := ih (by intro x hm; exact hx x (by simp [hm]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem seven_terms_fit (xs : List Nat) (hlen : xs.length ≤ 7)
    (hx : ∀ x ∈ xs, x ≤ (p-1)*tagMax) : xs.sum < word := by
  have hs := sum_le_length xs ((p-1)*tagMax) hx
  have hn := Nat.mul_le_mul_right ((p-1)*tagMax) hlen
  have hb : 7*((p-1)*tagMax) < word := by norm_num [p,tagMax,word]
  omega

theorem seven_prefixes_fit (xs : List Nat) (hlen : xs.length ≤ 7)
    (hx : ∀ x ∈ xs, x ≤ (p-1)*tagMax) (n : Nat) : (xs.take n).sum < word := by
  apply seven_terms_fit (xs.take n)
  · exact le_trans (by simp) hlen
  · intro x hm; exact hx x (List.mem_of_mem_take hm)

theorem seven_margin : word-7*((p-1)*tagMax)=1549236258180433762 := by
  norm_num [word,p,tagMax]
theorem eight_do_not_fit : word < 8*((p-1)*tagMax) := by
  norm_num [word,p,tagMax]

-- Reducing adjacent batches at a different boundary preserves the field sum.
theorem batch_mod (xs ys : List Nat) :
    (xs.sum%p+ys.sum%p)%p=(xs++ys).sum%p := by
  rw [List.sum_append]
  exact (Nat.add_mod xs.sum ys.sum p).symm

#print axioms raw_product_bound
#print axioms sum_le_length
#print axioms seven_terms_fit
#print axioms seven_prefixes_fit
#print axioms seven_margin
#print axioms eight_do_not_fit
#print axioms batch_mod
end AspisV8.CopyTagRange
