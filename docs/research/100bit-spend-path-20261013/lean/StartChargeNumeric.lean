import OracleDecisionMultiNumeric

set_option autoImplicit false
noncomputable section
namespace AspisR1.StartChargeNumeric
open OracleDecisionPrereqNumeric

abbrev totalBound (Q : Nat) := envelope Q 34 1161
abbrev Qmax := OracleDecisionMultiNumeric.safeMax

/-- Exact whole-experiment zero-query inequality, including all additive
allowances. This is scalar rational arithmetic, not a finite-field probe. -/
theorem zero_queries : totalBound 0 ≤ 1/(2:ℚ)^100 := by
  norm_num [totalBound,envelope,PerAttemptEnvelope.B,BinCombinedMerkleCollision.kappa,
    BinPerQueryNumeric.power454]

/-- The old upper range remains valid after removing terminal start charges;
there is no positive lower query bound. -/
theorem safe_range (Q : Nat) (hQ : Q ≤ Qmax) :
    totalBound Q ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) := by
  have hzero : gap 0 34 1161 ≤ 0 := by
    norm_num [gap,BinPerQueryNumeric.power454]
  have hend : gap Qmax 34 1161 ≤ 0 := by
    have h := OracleDecisionMultiNumeric.safe_edges.2.2.1
    rw [OracleDecisionMultiNumeric.start_delta] at h
    linarith
  have hg := gap_interval 0 Qmax Q 34 1161 (by norm_num [Qmax,OracleDecisionMultiNumeric.safeMax])
    (Nat.zero_le Q) hQ hzero hend
  rw [← envelope_gap] at hg
  linarith

#print axioms zero_queries
#print axioms safe_range
end AspisR1.StartChargeNumeric
end
