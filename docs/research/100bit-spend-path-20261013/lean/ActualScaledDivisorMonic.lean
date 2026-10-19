import ActualRawModRemainderCostBridge
import ActualRawModRemainderDegreeBridge
import ActualLongDivisionTotalCostV2

/-! Canonical divisor normalization properties for the retained raw remainder.
Independent of all commitment and proof-wire formats. -/
set_option autoImplicit false
namespace ActualScaledDivisorMonic
open CompPoly ActualRawModRemainderCostBridge
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem scaled_divisor_trim (q : CPolynomial.Raw F) :
    (monicScaledDivisor q).trim = monicScaledDivisor q :=
  CPolynomial.Raw.mul_is_trimmed _ _

theorem scaled_dividend_trim (p q : CPolynomial.Raw F) :
    (scaledDividend p q).trim = scaledDividend p q :=
  CPolynomial.Raw.mul_is_trimmed _ _

theorem scaled_divisor_leadingCoeff (q : CPolynomial.Raw F)
    (hq : q.trim = q) (hq0 : q ≠ (0 : CPolynomial.Raw F)) :
    (monicScaledDivisor q).leadingCoeff = 1 := by
  let qc : CPolynomial F := CPolynomial.ofArray q
  have hval : qc.val = q := hq
  have hqc : qc ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hval] at hv
    exact hq0 hv
  have hm := CPolynomial.leadingCoeff_inv_smul_monic qc hqc
  have hlead : qc.leadingCoeff = q.leadingCoeff := by
    simp [CPolynomial.leadingCoeff,CPolynomial.Raw.leadingCoeff,hval,hq]
  have hscaled : (qc.leadingCoeff⁻¹ • qc).val = monicScaledDivisor q := by
    change (CPolynomial.Raw.smul qc.leadingCoeff⁻¹ qc.val).trim = _
    rw [hval,hlead]
    exact (CPolynomial.Raw.C_mul_eq_smul_trim _ _).symm
  have hl : (qc.leadingCoeff⁻¹ • qc).leadingCoeff = 1 := by
    exact LawfulBEq.eq_of_beq hm
  change Array.getLastD (qc.leadingCoeff⁻¹ • qc).val 0 = 1 at hl
  rw [hscaled] at hl
  simpa only [CPolynomial.Raw.leadingCoeff,scaled_divisor_trim] using hl

theorem scaled_divisor_positive (q : CPolynomial.Raw F)
    (hq : q.trim = q) (hq0 : q ≠ (0 : CPolynomial.Raw F)) :
    0 < (monicScaledDivisor q).size := by
  have hm := scaled_divisor_leadingCoeff q hq hq0
  by_contra h
  have hs : (monicScaledDivisor q).size = 0 := by omega
  have he : monicScaledDivisor q = (#[] : CPolynomial.Raw F) :=
    Array.eq_empty_of_size_eq_zero hs
  rw [he] at hm
  have hz : CPolynomial.Raw.leadingCoeff (#[] : CPolynomial.Raw F) = 0 :=
    CPolynomial.Raw.leadingCoeff_zero
  rw [hz] at hm
  exact zero_ne_one hm

#print axioms scaled_divisor_trim
#print axioms scaled_dividend_trim
#print axioms scaled_divisor_leadingCoeff
#print axioms scaled_divisor_positive
end ActualScaledDivisorMonic
