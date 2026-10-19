import ActualRawModRemainderSizeBound
import ActualRawModRemainderCostBridge
import CompPolyModularRemainderDegree
import ActualModularProductDegreeBound
import CompPoly.Univariate.Raw.Modular

namespace ActualRawModRemainderDegreeBridge
open CompPoly Polynomial
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private theorem raw_monicNormalize_trim (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.monicNormalize p).trim = CPolynomial.Raw.monicNormalize p := by
  unfold CPolynomial.Raw.monicNormalize
  let q := p.trim
  by_cases hz : q == (0 : CPolynomial.Raw F)
  · have hq : q = 0 := by simpa using hz
    have hp : p.trim = (#[] : CPolynomial.Raw F) := by simpa [q] using hq
    simp [hp, CPolynomial.Raw.Trim.canonical_empty]
  · have hq : q ≠ (0 : CPolynomial.Raw F) := by
      intro h
      exact hz (by simp [h])
    have hp : ¬p.trim = (#[] : CPolynomial.Raw F) := by
      intro h
      exact hq (by simpa [q] using h)
    simp [hp]
    change (CPolynomial.Raw.mk (Array.map (fun r ↦ q.leadingCoeff⁻¹ * r) p.trim)).trim =
      CPolynomial.Raw.mk (Array.map (fun r ↦ q.leadingCoeff⁻¹ * r) p.trim)
    apply CPolynomial.Raw.Trim.non_zero_map (fun r ↦ q.leadingCoeff⁻¹ * r)
    · intro r hr
      rcases mul_eq_zero.mp hr with hi | hr0
      · have hlead : q.leadingCoeff = 0 := inv_eq_zero.mp hi
        have hcanon : q.trim = q := by simpa [q] using CPolynomial.Raw.Trim.trim_twice p
        have hcrit := (CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero
          (p := q)).mp hcanon
        rcases hcrit with he | hl
        · have hempty : q = (#[] : CPolynomial.Raw F) := Array.eq_empty_of_size_eq_zero he
          exact False.elim (hq hempty)
        · unfold CPolynomial.Raw.leadingCoeff at hlead
          rw [hcanon] at hlead
          exact (hl hlead).elim
      · exact hr0
    · simpa [q] using CPolynomial.Raw.Trim.trim_twice p

private theorem raw_monicNormalize_nonzero {p : CPolynomial.Raw F}
    (hp : p.trim ≠ (0 : CPolynomial.Raw F)) :
    CPolynomial.Raw.monicNormalize p ≠ 0 := by
  unfold CPolynomial.Raw.monicNormalize
  by_cases hz : p.trim == (0 : CPolynomial.Raw F)
  · have heq : p.trim = 0 := by simpa using hz
    exact (hp heq).elim
  · rw [if_neg hz]
    intro h
    have hsize_smul :
        (CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim).size = p.trim.size := by
      simp [CPolynomial.Raw.smul]
    change CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim = 0 at h
    rw [h] at hsize_smul
    have hs : p.trim.size = 0 := by simpa using hsize_smul.symm
    exact hp (Array.eq_empty_of_size_eq_zero hs)

private theorem raw_monicNormalize_poly_monic {p : CPolynomial.Raw F}
    (hp : p.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly.Monic := by
  rw [show (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly =
      normalize (CPolynomial.ofArray p).toPoly from by
        have h := CPolynomial.monicNormalize_toPoly_eq_normalize (CPolynomial.ofArray p)
        unfold CPolynomial.monicNormalize at h
        unfold CPolynomial.ofArray at h
        rw [show CPolynomial.Raw.monicNormalize p.trim = CPolynomial.Raw.monicNormalize p from by
          unfold CPolynomial.Raw.monicNormalize
          rw [CPolynomial.Raw.Trim.trim_twice]] at h
        exact h]
  have hpC : CPolynomial.ofArray p ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    unfold CPolynomial.ofArray at hv
    exact hp hv
  have hpPoly : (CPolynomial.ofArray p).toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff (CPolynomial.ofArray p)).not.mpr hpC
  exact Polynomial.monic_normalize hpPoly

private theorem scaledDivisor_eq_normalize (q : CPolynomial.Raw F)
    (hq : q.trim = q) (hq0 : q ≠ (0 : CPolynomial.Raw F)) :
    ActualRawModRemainderCostBridge.monicScaledDivisor q =
      CPolynomial.Raw.monicNormalize q := by
  change CPolynomial.Raw.C q.leadingCoeff⁻¹ * q = CPolynomial.Raw.monicNormalize q
  rw [CPolynomial.Raw.C_mul_eq_smul_trim]
  have hqTrim0 : q.trim ≠ (#[] : CPolynomial.Raw F) := by simpa [hq] using hq0
  have hqne : q.trim ≠ (#[] : CPolynomial.Raw F) := hqTrim0
  have hnorm : CPolynomial.Raw.monicNormalize q =
      CPolynomial.Raw.smul q.leadingCoeff⁻¹ q := by
    unfold CPolynomial.Raw.monicNormalize
    rw [if_neg]
    · rw [hq]
      rfl
    · simpa using hqne
  rw [← hnorm]
  exact raw_monicNormalize_trim q

/-- The exact raw `%` implementation shrinks the returned remainder to at most
the canonical divisor length. This supplies the Euclidean size invariant. -/
theorem rawMod_size_le_divisor (p q : CPolynomial.Raw F)
    (hp : p.trim = p) (hq : q.trim = q) (hq0 : q ≠ (0 : CPolynomial.Raw F)) :
    (p % q).size ≤ q.size := by
  rw [ActualRawModRemainderCostBridge.rawMod_eq_scaledMonicRemainder,
    scaledDivisor_eq_normalize q hq hq0]
  have hpScaled :
      (ActualRawModRemainderCostBridge.scaledDividend p q).trim =
        ActualRawModRemainderCostBridge.scaledDividend p q := by
    change (CPolynomial.Raw.C q.leadingCoeff⁻¹ * p).trim =
      CPolynomial.Raw.C q.leadingCoeff⁻¹ * p
    exact CPolynomial.Raw.mul_is_trimmed _ _
  have hnormTrim : (CPolynomial.Raw.monicNormalize q).trim =
      CPolynomial.Raw.monicNormalize q := raw_monicNormalize_trim q
  have hqTrim0 : q.trim ≠ 0 := by simpa [hq] using hq0
  have hnorm0 : CPolynomial.Raw.monicNormalize q ≠ 0 := raw_monicNormalize_nonzero hqTrim0
  have hnormMonic : (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize q)).monic = true := by
    apply (CPolynomial.monic_toPoly_iff _).mpr
    exact raw_monicNormalize_poly_monic hqTrim0
  have hrem := CompPolyModularRemainderDegree.raw_modByMonic_size_le
    (ActualRawModRemainderCostBridge.scaledDividend p q)
    (CPolynomial.Raw.monicNormalize q) hpScaled hnormTrim hnorm0 hnormMonic
  rw [ActualModularProductDegreeBound.monicNormalize_size_eq_trim q hqTrim0] at hrem
  simpa [hq] using hrem

#print axioms rawMod_size_le_divisor
end ActualRawModRemainderDegreeBridge
