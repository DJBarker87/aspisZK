import AspisFormal.V5FriCircleEncoderDistance

/-! The unsquared fractional lift is an involution up to its explicit
degree-dependent scalar. The proof uses polynomial evaluation on the existing
stereographic sample set, without expanding the defining finite sum. -/
set_option autoImplicit false
namespace AspisV5FriCircleEncoderDistance

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [NeZero (2 : K)]

theorem fractionalLift_involution (d : Nat) (hcard : d + 1 < Fintype.card K)
    (p : K[X]) (hp : p.natDegree ≤ d) :
    fractionalLift d (fractionalLift d p) = Polynomial.C ((2 : K) ^ d) * p := by
  classical
  let sample := (Finset.univ : Finset K).erase (-1)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (fractionalLift d (fractionalLift d p))
    (Polynomial.C ((2 : K) ^ d) * p) sample
  · intro x hx
    have hxneg : x ≠ -1 := by
      simpa only [sample, Finset.mem_erase, Finset.mem_univ, and_true] using hx
    have hden : (1 : K) + x ≠ 0 := by
      intro h
      apply hxneg
      linear_combination h
    let u : K := (1 - x) / (1 + x)
    have hinv := fractional_involution x hxneg
    have hdenU : 1 + u ≠ 0 := by simpa [u] using hinv.1
    have hreturn : (1 - u) / (1 + u) = x := by simpa [u] using hinv.2
    have hprod : (1 + u) * (1 + x) = 2 := by
      dsimp [u]
      field_simp [hden]
      ring
    have hpow : (1 + u) ^ d * (1 + x) ^ d = (2 : K) ^ d := by
      rw [← mul_pow, hprod]
    have houter :
        (fractionalLift d (fractionalLift d p)).eval x =
          (fractionalLift d p).eval u * (1 + x) ^ d := by
      rw [fractionalLift_eval]
      exact mobiusLift_eval_div d (fractionalLift d p)
        (fractionalLift_natDegree_le d p) (1 - x) (1 + x) hden
    have hinner : (fractionalLift d p).eval u = p.eval x * (1 + u) ^ d := by
      rw [fractionalLift_eval]
      have h := mobiusLift_eval_div d p hp (1 - u) (1 + u) hdenU
      rw [hreturn] at h
      exact h
    have hleft :
        (fractionalLift d (fractionalLift d p)).eval x =
          (2 : K) ^ d * p.eval x := by
      rw [houter, hinner]
      calc
        p.eval x * (1 + u) ^ d * (1 + x) ^ d =
            p.eval x * ((1 + u) ^ d * (1 + x) ^ d) := by ring
        _ = p.eval x * (2 : K) ^ d := by rw [hpow]
        _ = (2 : K) ^ d * p.eval x := by ring
    have hright : (Polynomial.C ((2 : K) ^ d) * p).eval x =
        (2 : K) ^ d * p.eval x := by simp
    rw [hleft, hright]
  · have hleft :
        (fractionalLift d (fractionalLift d p)).natDegree ≤ d :=
      fractionalLift_natDegree_le d (fractionalLift d p)
    have hC : (Polynomial.C ((2 : K) ^ d)).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_C]
    have hright : (Polynomial.C ((2 : K) ^ d) * p).natDegree ≤ d := by
      calc
        (Polynomial.C ((2 : K) ^ d) * p).natDegree ≤
            (Polynomial.C ((2 : K) ^ d)).natDegree + p.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 0 + d := Nat.add_le_add hC hp
        _ = d := by omega
    have hcardSample : sample.card = Fintype.card K - 1 := by simp [sample]
    rw [hcardSample]
    have hmax : max (fractionalLift d (fractionalLift d p)).natDegree
        (Polynomial.C ((2 : K) ^ d) * p).natDegree ≤ d := max_le hleft hright
    omega

#print axioms fractionalLift_involution

end AspisV5FriCircleEncoderDistance
