import FoldStoredGeometry

/-! Symbolic 9+9-bit factorization behind fast_domain.rs. Literal table
contents enter only via named hypotheses; their independent arithmetic
validation is recorded in the evidence directory. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldFactoredDomain
open AspisCircleGroupOrder AspisV5FriBitReverse
open AspisR1.FoldStoredGeometry

theorem reverse_split (n m u : Nat) :
    reverseBits (n + m) u =
      reverseBits n u * 2 ^ m + reverseBits m (u / 2 ^ n) := by
  induction n generalizing u with
  | zero => simp [reverseBits]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    rw [reverseBits, ih, reverseBits]
    rw [Nat.pow_add, Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [show 2 * (2 ^ n) = 2 ^ n * 2 by omega]
    ring

/-- Higher input bits do not affect fixed-width reversal. -/
theorem reverse_mod (n u : Nat) : reverseBits n (u % 2 ^ n) = reverseBits n u := by
  induction n generalizing u with
  | zero => simp [reverseBits]
  | succ n ih =>
    rw [reverseBits, reverseBits]
    have hm : (u % 2 ^ (n + 1)) % 2 = u % 2 := by
      rw [Nat.pow_succ]
      exact Nat.mod_mod_of_dvd u (Nat.dvd_mul_left 2 (2 ^ n))
    have hd : (u % 2 ^ (n + 1)) / 2 = (u / 2) % 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.mod_mul_right_div_self u 2 (2 ^ n)
    rw [hm, hd, ih]

/-- The tables split the stored index as low nine bits and high nine bits. -/
theorem reverse18_split (u : Nat) :
    reverseBits 18 u = 512 * reverseBits 9 (u % 512) +
      reverseBits 9 (u / 512) := by
  have h := reverse_split 9 9 u
  have hm : reverseBits 9 (u % 512) = reverseBits 9 u := reverse_mod 9 u
  rw [hm]
  simpa [Nat.mul_comm] using h

def tableA (lo : Nat) : C := g ^ (1024 + 2097152 * (reverseBits 9 lo : Int))
def tableB (hi : Nat) : C := g ^ (4096 * (reverseBits 9 hi : Int))

theorem factored_fibre (u : Fin 262144) :
    tableA (u.val % 512) * tableB (u.val / 512) = sourceFibre u := by
  unfold tableA tableB sourceFibre
  rw [← zpow_add, reverse18_split]
  apply congrArg (fun n : Int => g ^ n)
  push_cast
  ring

/-- Explicit boundary for the extracted/constant-table refinement. -/
theorem tables_to_stored (a b : Nat → C)
    (hA : ∀ lo, lo < 512 → a lo = tableA lo)
    (hB : ∀ hi, hi < 512 → b hi = tableB hi) (u : Fin 262144) :
    a (u.val % 512) * b (u.val / 512) =
      AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 u := by
  rw [hA _ (Nat.mod_lt _ (by decide)), hB _ (by have := u.isLt; omega),
    factored_fibre, fibre_eq_stored]

#print axioms reverse_split
#print axioms reverse_mod
#print axioms reverse18_split
#print axioms factored_fibre
#print axioms tables_to_stored
end AspisR1.FoldFactoredDomain
