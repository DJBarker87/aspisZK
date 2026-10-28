import NDO_JHk_Line05
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs05
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨650520807,233937645⟩,⟨383112235,1195341269⟩⟩,⟨⟨1086575322,1528770998⟩,⟨1153081827,2104919066⟩⟩⟩
def power : K := ⟨⟨973458266,1691467449⟩,⟨1765941834,1051698078⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs04.rhs+LiteralOpeningView.eK JHk_Rhs04.power*JHk_Line05.value=rhs := by
  change (⟨⟨⟨1912763292,1473059900⟩,⟨1095070407,756137035⟩⟩,⟨⟨279988608,201928833⟩,⟨1764268037,240284230⟩⟩⟩ : FE)+⟨⟨⟨741587425,1272351995⟩,⟨1232633493,701380605⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨1564019087,1397113853⟩,⟨945795750,1095455810⟩⟩,⟨⟨1069439448,1241956085⟩,⟨611435966,1657284701⟩⟩⟩=⟨⟨⟨650520807,233937645⟩,⟨383112235,1195341269⟩⟩,⟨⟨1086575322,1528770998⟩,⟨1153081827,2104919066⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs04.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨741587425,1272351995⟩,⟨1232633493,701380605⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨973458266,1691467449⟩,⟨1765941834,1051698078⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs05
end
