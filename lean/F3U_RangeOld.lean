import F3U_Range
import OracleDecisionMultiNumeric
set_option autoImplicit false
namespace AspisR1.F3U_RangeOld

theorem original_model_range_fails :
    (OracleDecisionMultiNumeric.safeMax+1:Rat)*(1/(2:Rat)^100)<
      F3T_Numeric.total OracleDecisionMultiNumeric.safeMax := by
  norm_num [F3T_Numeric.total,F3T_Numeric.collisionLoss,F3T_Numeric.accountLoss,
    OracleDecisionMultiNumeric.safeMax,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

#print axioms original_model_range_fails
end AspisR1.F3U_RangeOld
