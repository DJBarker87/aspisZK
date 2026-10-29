import R1Z.PV_RunJoin_FixtureRecords
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Sentinel
open R0P
abbrev Scalar := PV_RunJoin_FixtureRecords.M
def s_0_0 : Fin 16 → Scalar := ![501,518,535,552,569,586,603,620,1095958531,18,0,0,0,0,0,0]
def s_0_1 : Fin 16 → Scalar := ![44444874,1095970125,1095970260,1140403420,44445350,1095970601,1095970736,1140403896,88874700,44441351,44441417,133308077,44441231,1095966431,1095966515,1140399760]
theorem round_0_1 : poseidonExternalLinear s_0_0 = s_0_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_1
def s_0_2 : Fin 16 → Scalar := ![1605081258,401532894,1046616540,1999259901,689556497,1136850762,1153214673,2066016037,854320284,593842034,2036373893,1901695727,1164210139,193649501,1249932995,675061968]
theorem round_0_2 : poseidonFullRound s_0_1 (poseidonExternalInitial 0) = s_0_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_2
end R1Z.PV_RunJoin_Sentinel
