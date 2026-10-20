import OracleDecisionPrereqNumeric

/-! Scalar consequences of the unconditional shared-decision start bound.
This does not port a security theorem or assert that the bound is sharp. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiNumeric
open OracleDecisionPrereqNumeric

def safeMax : Nat := 14777960484892959601791002642008314224629686649

theorem safe_edges : 0 < gap 31 1080 1161 ∧ gap 32 1080 1161 ≤ 0 ∧
    gap safeMax 1080 1161 ≤ 0 ∧ 0 < gap (safeMax+1) 1080 1161 := by
  norm_num [gap, safeMax, BinPerQueryNumeric.power454]

theorem safe_range (Q : Nat) (hlo : 32 ≤ Q) (hhi : Q ≤ safeMax) :
    envelope Q 1080 1161 ≤ (Q+1 : ℚ)*(1/(2:ℚ)^100) := by
  have hg := gap_interval 32 safeMax Q 1080 1161 (by norm_num [safeMax])
    hlo hhi safe_edges.2.1 safe_edges.2.2.1
  rw [← envelope_gap] at hg
  linarith

theorem start_delta (x : ℚ) :
    gap x 1080 1161 = gap x 34 1161 + 1046*15/(2:ℚ)^109 := by
  simp only [gap, BinPerQueryNumeric.power454]
  push_cast
  ring

theorem safe_zero_fails : (1:ℚ)/(2:ℚ)^100 < envelope 0 1080 1161 := by
  have hg : 0 < gap 0 1080 1161 := by norm_num [gap, BinPerQueryNumeric.power454]
  have he : envelope 0 1080 1161 - 1/(2:ℚ)^100 = gap 0 1080 1161 := by
    simpa only [Nat.cast_zero, zero_add, one_mul] using envelope_gap 0 1080 1161
  rw [← he] at hg
  linarith

theorem maximum_shift : safeMax + 31 = BinPerQueryNumeric.Qmax := by
  norm_num [safeMax, BinPerQueryNumeric.Qmax]

/-- A shifted ledger polynomial can keep its degree and multiply its
coefficient by at most 2^d. This does not instantiate ledger adequacy. -/
theorem ledger_polynomial (Q d : Nat) :
    (Q + 2322)^d ≤ 2^d * (Q + 1161)^d := by
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega) d

#print axioms safe_edges
#print axioms safe_range
#print axioms start_delta
#print axioms safe_zero_fails
#print axioms maximum_shift
#print axioms ledger_polynomial
end AspisR1.OracleDecisionMultiNumeric
end
