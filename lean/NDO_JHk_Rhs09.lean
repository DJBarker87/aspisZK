import NDO_JHk_Line09
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs09
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨1460949651,1897962060⟩,⟨2049955535,440526196⟩⟩,⟨⟨1936630531,105592648⟩,⟨1567937285,2130692216⟩⟩⟩
def power : K := ⟨⟨1007926423,526023474⟩,⟨347718395,268326460⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs08.rhs+LiteralOpeningView.eK JHk_Rhs08.power*JHk_Line09.value=rhs := by
  change (⟨⟨⟨1609915618,1406937229⟩,⟨1284218296,550047463⟩⟩,⟨⟨1722769472,1118979547⟩,⟨444162423,1656256757⟩⟩⟩ : FE)+⟨⟨⟨160410907,665703601⟩,⟨1363748181,807933172⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨795046778,1374188295⟩,⟨460169651,568293753⟩⟩,⟨⟨1033592440,750200039⟩,⟨1739915931,1242973730⟩⟩⟩=⟨⟨⟨1460949651,1897962060⟩,⟨2049955535,440526196⟩⟩,⟨⟨1936630531,105592648⟩,⟨1567937285,2130692216⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs08.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨160410907,665703601⟩,⟨1363748181,807933172⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨1007926423,526023474⟩,⟨347718395,268326460⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
theorem retained : rhs=CheckpointBytes5Output.ofE JFq_Rhs.scalar := rfl
#print axioms retained
end AspisR1.JHk_Rhs09
end
