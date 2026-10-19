import ActualRawModRemainderCostBridge
import CompPoly.Univariate.Raw.Modular

namespace ActualRawModRemainderSizeBound
open CompPoly
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

theorem scaledDividend_size_le (p q : CPolynomial.Raw F) :
    (ActualRawModRemainderCostBridge.scaledDividend p q).size ≤ p.size := by
  change (CPolynomial.Raw.C q.leadingCoeff⁻¹ * p).size ≤ p.size
  rw [CPolynomial.Raw.C_mul_eq_smul_trim]
  exact (CPolynomial.Raw.Trim.size_le_size _).trans (by simp [CPolynomial.Raw.smul])

theorem scaledDivisor_size_le (q : CPolynomial.Raw F) :
    (ActualRawModRemainderCostBridge.monicScaledDivisor q).size ≤ q.size := by
  change (CPolynomial.Raw.C q.leadingCoeff⁻¹ * q).size ≤ q.size
  rw [CPolynomial.Raw.C_mul_eq_smul_trim]
  exact (CPolynomial.Raw.Trim.size_le_size _).trans (by simp [CPolynomial.Raw.smul])

#print axioms scaledDividend_size_le
#print axioms scaledDivisor_size_le
end ActualRawModRemainderSizeBound
