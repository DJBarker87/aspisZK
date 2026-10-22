import R1Z.ProverCommitAudit51
import R1Z.ProverCommitBind51
import R1Z.ProverCommitClaimMap51
import R1Z.ProverCommitCoefficientModel51
import R1Z.ProverCommitCoefficients51
import R1Z.ProverCommitConcreteMask51
import R1Z.ProverCommitExtraCaller51
import R1Z.ProverCommitExtraClaim51
import R1Z.ProverCommitExtraMath51
import R1Z.ProverCommitExtraModel51
import R1Z.ProverCommitHalfPrefix51
import R1Z.ProverCommitInverseCases51
import R1Z.ProverCommitLinearOracle51
import R1Z.ProverCommitMaskArithmetic51
import R1Z.ProverCommitMaskCaller51
import R1Z.ProverCommitMaskColumns51
import R1Z.ProverCommitMaskInventory51
import R1Z.ProverCommitMaskMap51
import R1Z.ProverCommitMaskProducer51
import R1Z.ProverCommitMaskRead51
import R1Z.ProverCommitMaskSchedule51
import R1Z.ProverCommitMaskWide51
import R1Z.ProverCommitMaskWrites51
import R1Z.ProverCommitQBasis51
import R1Z.ProverCommitTerminalArithmetic51
import R1Z.ProverCommitTerminalEquality51
import R1Z.ProverCommitTerminalFactor51
import R1Z.ProverCommitTerminalHead51
import R1Z.ProverCommitTerminalMath51
import R1Z.ProverCommitTerminalProduct51
import R1Z.ProverCommitTerminalSuffix51
import R1Z.ProverCommitWideBasis51
import R1Z.ProverCommitWriteMath51

/-! Final combined import and axiom audit of this task’s accepted cone.
Not a replay of the unavailable terminal dependency closure. -/
#print axioms R1Z.ProverCommitBind51.three
#print axioms R1Z.ProverCommitClaimMap51.dot
#print axioms R1Z.ProverCommitClaimMap51.weight
#print axioms R1Z.ProverCommitClaimMap51.carry
#print axioms R1Z.ProverCommitClaimMap51.successor
#print axioms R1Z.ProverCommitClaimMap51.absorption
#print axioms R1Z.ProverCommitClaimMap51.points
#print axioms R1Z.ProverCommitClaimMap51.claims
#print axioms R1Z.ProverCommitClaimMap51.libra
#print axioms R1Z.ProverCommitClaimMap51.extra
#print axioms R1Z.ProverCommitCoefficientModel51.row
#print axioms R1Z.ProverCommitCoefficientModel51.exact_result
#print axioms R1Z.ProverCommitCoefficients51.cell
#print axioms R1Z.ProverCommitCoefficients51.go
#print axioms R1Z.ProverCommitCoefficients51.exact_result
#print axioms R1Z.ProverCommitConcreteMask51.exact_result
#print axioms R1Z.ProverCommitExtraCaller51.source_array
#print axioms R1Z.ProverCommitExtraCaller51.exact_result
#print axioms R1Z.ProverCommitExtraClaim51.exact_result
#print axioms R1Z.ProverCommitExtraMath51.source_polynomial
#print axioms R1Z.ProverCommitExtraMath51.dot_polynomial
#print axioms R1Z.ProverCommitExtraModel51.dot_generic
#print axioms R1Z.ProverCommitExtraModel51.dot_value
#print axioms R1Z.ProverCommitExtraModel51.exact_result
#print axioms R1Z.ProverCommitHalfPrefix51.none_iff
#print axioms R1Z.ProverCommitHalfPrefix51.some_nonhalf
#print axioms R1Z.ProverCommitHalfPrefix51.inverse
#print axioms R1Z.ProverCommitInverseCases51.zero_reject
#print axioms R1Z.ProverCommitInverseCases51.some_nonzero
#print axioms R1Z.ProverCommitInverseCases51.none_iff
#print axioms R1Z.ProverCommitLinearOracle51.exact_result
#print axioms R1Z.ProverCommitMaskArithmetic51.input_polynomial
#print axioms R1Z.ProverCommitMaskArithmetic51.caller
#print axioms R1Z.ProverCommitMaskCaller51.exact_result
#print axioms R1Z.ProverCommitMaskColumns51.index
#print axioms R1Z.ProverCommitMaskColumns51.go
#print axioms R1Z.ProverCommitMaskColumns51.exact_result
#print axioms R1Z.ProverCommitMaskInventory51.polynomial
#print axioms R1Z.ProverCommitMaskMap51.linear
#print axioms R1Z.ProverCommitMaskMap51.basis
#print axioms R1Z.ProverCommitMaskMap51.multiply_basis
#print axioms R1Z.ProverCommitMaskMap51.value
#print axioms R1Z.ProverCommitMaskProducer51.word_value
#print axioms R1Z.ProverCommitMaskProducer51.exact_result
#print axioms R1Z.ProverCommitMaskRead51.claims_value
#print axioms R1Z.ProverCommitMaskRead51.exact_result
#print axioms R1Z.ProverCommitMaskSchedule51.bound
#print axioms R1Z.ProverCommitMaskSchedule51.injective
#print axioms R1Z.ProverCommitMaskSchedule51.first
#print axioms R1Z.ProverCommitMaskSchedule51.second
#print axioms R1Z.ProverCommitMaskSchedule51.omitted
#print axioms R1Z.ProverCommitMaskWide51.exact_result
#print axioms R1Z.ProverCommitMaskWrites51.index
#print axioms R1Z.ProverCommitMaskWrites51.decode_update
#print axioms R1Z.ProverCommitMaskWrites51.go
#print axioms R1Z.ProverCommitQBasis51.base_coordinates
#print axioms R1Z.ProverCommitQBasis51.basis
#print axioms R1Z.ProverCommitQBasis51.basis_i
#print axioms R1Z.ProverCommitQBasis51.basis_u
#print axioms R1Z.ProverCommitTerminalArithmetic51.exact_result
#print axioms R1Z.ProverCommitTerminalArithmetic51.zero_helper
#print axioms R1Z.ProverCommitTerminalEquality51.exact_result
#print axioms R1Z.ProverCommitTerminalFactor51.exact_result
#print axioms R1Z.ProverCommitTerminalHead51.exact_value
#print axioms R1Z.ProverCommitTerminalMath51.product_range
#print axioms R1Z.ProverCommitTerminalMath51.product_model
#print axioms R1Z.ProverCommitTerminalProduct51.go
#print axioms R1Z.ProverCommitTerminalSuffix51.exact_result
#print axioms R1Z.ProverCommitWideBasis51.basis_i
#print axioms R1Z.ProverCommitWideBasis51.basis_u
#print axioms R1Z.ProverCommitWriteMath51.fill_eq
#print axioms R1Z.ProverCommitWriteMath51.coeff_at
#print axioms R1Z.ProverCommitWriteMath51.coeff_outside
