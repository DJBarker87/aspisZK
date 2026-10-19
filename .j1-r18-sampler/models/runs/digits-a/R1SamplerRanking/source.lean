import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace AspisR1.SamplerRanking

def digitsRank (p n : Nat) : (Fin n → Fin p) ≃ Fin (p ^ n) :=
  finFunctionFinEquiv

private theorem pow_pos_nat {p n : Nat} (hp : 0 < p) : 0 < p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih hp

theorem digitsRank_symm_apply_val {p n : Nat} (_hp : 0 < p)
    (x : Fin (p ^ n)) (i : Fin n) :
    ((digitsRank p n).symm x i).val = x.val / p ^ i.val % p := by
  simp [digitsRank]

theorem digitsRank_value {p n : Nat} (f : Fin n → Fin p) :
    (digitsRank p n f).val = ∑ i : Fin n, (f i).val * p ^ i.val := by
  exact finFunctionFinEquiv_apply f

def canonicalDigits (p n x : Nat) (hp : 0 < p) : Fin n → Fin p :=
  fun i => ⟨x / p ^ i.val % p, Nat.mod_lt _ hp⟩

theorem canonicalDigits_eq_rank_symm {p n x : Nat} (hp : 0 < p) :
    canonicalDigits p n x hp =
      (digitsRank p n).symm ⟨x % p ^ n, Nat.mod_lt _ (pow_pos_nat hp)⟩ := by
  funext i
  apply Fin.ext
  change x / p ^ i.val % p = _
  rw [digitsRank_symm_apply_val hp]
  have hle : i.val ≤ n := Nat.le_of_lt i.is_lt
  have hsum : i.val + (n - i.val) = n := Nat.add_sub_of_le hle
  have hpow : p ^ i.val * p ^ (n - i.val) = p ^ n := by
    rw [← Nat.pow_add, hsum]
  have hquot : x % p ^ n / p ^ i.val =
      x / p ^ i.val % p ^ (n - i.val) := by
    rw [← hpow]
    exact Nat.mod_mul_right_div_self x (p ^ i.val) (p ^ (n - i.val))
  have htail : 0 < n - i.val := Nat.sub_pos_of_lt i.is_lt
  have hdvd : p ∣ p ^ (n - i.val) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htail) with ⟨k, hk⟩
    rw [hk, pow_succ]
    exact ⟨p ^ k, by rw [Nat.mul_comm]⟩
  rw [hquot, Nat.mod_mod_of_dvd _ hdvd]

#print axioms digitsRank_symm_apply_val
#print axioms digitsRank_value
#print axioms canonicalDigits_eq_rank_symm

end AspisR1.SamplerRanking
