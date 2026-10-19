import CompPoly.Univariate.Raw.Proofs
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Univariate.ToPoly.Equiv
import Lean.Elab.Tactic.Omega

namespace RawMulSizeBound
open CompPoly
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem raw_toPoly_natDegree_le_size (p : CPolynomial.Raw F) :
    p.toPoly.natDegree ≤ p.size := by
  by_cases hz : p.trim.size = 0
  · have hpTrim : p.trim = (#[] : CPolynomial.Raw F) :=
      Array.eq_empty_of_size_eq_zero hz
    have hp : p.toPoly = 0 := by
      rw [← CPolynomial.Raw.toPoly_trim, hpTrim]
      simp [CPolynomial.Raw.toPoly, CPolynomial.Raw.eval₂]
    simp [hp]
  · have hpos : 0 < p.trim.size := Nat.pos_of_ne_zero hz
    exact le_trans (Nat.le_of_lt
      (CPolynomial.Raw.toPoly_natDegree_lt_trim_size_of_pos p hpos))
      (CPolynomial.Raw.Trim.size_le_size p)

/-- The actual naive raw convolution returns an array no longer than the sum
of the operand lengths plus one. -/
theorem raw_mul_size_le (p q : CPolynomial.Raw F) :
    (p * q).size ≤ p.size + q.size + 1 := by
  let z := p * q
  have hcanon : z.trim = z := by
    simpa [z] using CPolynomial.Raw.mul_is_trimmed p q
  by_cases hz : z.toPoly = 0
  · have hround := CPolynomial.Raw.toImpl_toPoly (R := F) z
    rw [hz] at hround
    have htrim : z.trim = (0 : CPolynomial.Raw F) := by
      simpa [Polynomial.toImpl] using hround.symm
    have hzraw : z = 0 := hcanon.symm.trans htrim
    simp [z, hzraw]
  · have hround : z.toPoly.toImpl = z := by
      rw [CPolynomial.Raw.toImpl_toPoly, hcanon]
    have hsize : z.toPoly.toImpl.size = z.size := congrArg Array.size hround
    rcases CPolynomial.Raw.toImpl_elim z.toPoly with ⟨hzero, _himpl⟩ | ⟨_hnz, himpl⟩
    · exact (hz hzero).elim
    · have himplSize : z.toPoly.toImpl.size = z.toPoly.natDegree + 1 := by
        simp [himpl]
      have hdeg : z.toPoly.natDegree ≤ p.toPoly.natDegree + q.toPoly.natDegree := by
        change (p * q).toPoly.natDegree ≤ p.toPoly.natDegree + q.toPoly.natDegree
        rw [CPolynomial.Raw.toPoly_mul]
        exact Polynomial.natDegree_mul_le
      have hpdeg := raw_toPoly_natDegree_le_size p
      have hqdeg := raw_toPoly_natDegree_le_size q
      calc
        z.size = z.toPoly.toImpl.size := hsize.symm
        _ = z.toPoly.natDegree + 1 := himplSize
        _ ≤ p.size + q.size + 1 := by omega

#print axioms raw_toPoly_natDegree_le_size
#print axioms raw_mul_size_le
end RawMulSizeBound
