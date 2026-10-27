import R1Z.PV_RunJoin_FixtureRecords
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
abbrev Scalar := PV_RunJoin_FixtureRecords.M
def s_0_0 : Fin 16 → Scalar := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1095962629]
def s_0_1 : Fin 16 → Scalar := ![1095962629,1095962629,1140404240,44441611,1095962629,1095962629,1140404240,44441611,1095962629,1095962629,1140404240,44441611,44441611,44441611,133324833,88883222]
theorem round_0_1 : poseidonExternalLinear s_0_0 = s_0_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_1
def s_0_2 : Fin 16 → Scalar := ![1413039620,424771284,357939999,264476178,1354857477,887956143,718525645,58980122,1099711526,1390287472,1610966340,1397489758,2119675089,1469160516,86623777,882586544]
theorem round_0_2 : poseidonFullRound s_0_1 (poseidonExternalInitial 0) = s_0_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_2
end R1Z.PV_RunJoin_RootModel
