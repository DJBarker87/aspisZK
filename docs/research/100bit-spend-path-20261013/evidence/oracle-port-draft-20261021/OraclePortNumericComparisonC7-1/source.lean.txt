import OraclePortHeadline

/-! Exact comparison with the retained pure-decision numeric envelope.
No large concrete recurrence is reduced. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortNumericComparisonC7

theorem envelope_delta (Q : Nat) :
    OraclePortHeadline.totalBound Q = BinPerQueryNumeric.totalBound Q +
      1046*PerAttemptEnvelope.B := by
  unfold OraclePortHeadline.totalBound OracleDecisionPrereqNumeric.envelope
    BinPerQueryNumeric.totalBound
  push_cast
  ring

theorem maximum_shift : OracleDecisionMultiNumeric.safeMax + 31 = BinPerQueryNumeric.Qmax :=
  OracleDecisionMultiNumeric.maximum_shift

/-- The larger log domain multiplies the cubic budget by at most eight. -/
theorem cubic_shift (Q scale : Nat) :
    4*scale^3*(Q+2323)^3 ≤ 8*(4*scale^3*(Q+1162)^3) := by
  calc
    4*scale^3*(Q+2323)^3 ≤ 4*scale^3*(2*(Q+1162))^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    _ = _ := by ring

#print axioms envelope_delta
#print axioms maximum_shift
#print axioms cubic_shift
end AspisR1.OraclePortNumericComparisonC7
end
