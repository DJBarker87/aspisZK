import RPz8_F3U_Numeric
import OracleDecisionPrereqNumeric
set_option autoImplicit false
namespace AspisR1.F3U_RangePolynomial

def gap (x : Rat) : Rat :=
  6*((x+1161)^2+(x+2965)^2)/(2:Rat)^256+(x+34)*15/(2:Rat)^109+
    1/(2:Rat)^126+1/(2:Rat)^454-(x+1)/(2:Rat)^100

theorem total_gap (Q : Nat) : F3T_Numeric.total Q-(Q+1:Rat)*(1/(2:Rat)^100)=gap Q := by
  unfold F3T_Numeric.total F3T_Numeric.collisionLoss F3T_Numeric.accountLoss gap
  have b : PerAttemptEnvelope.B=15/(2:Rat)^109 := by norm_num [PerAttemptEnvelope.B]
  rw [b]
  push_cast
  ring

#print axioms total_gap
end AspisR1.F3U_RangePolynomial
