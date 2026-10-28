import NDO_JHk_Line06
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs06
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨206822164,239294967⟩,⟨1701938808,1166648691⟩⟩,⟨⟨1926633681,224622122⟩,⟨1395774668,56394308⟩⟩⟩
def power : K := ⟨⟨287584799,1156076550⟩,⟨2035531565,441759647⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs05.rhs+LiteralOpeningView.eK JHk_Rhs05.power*JHk_Line06.value=rhs := by
  change (⟨⟨⟨650520807,233937645⟩,⟨383112235,1195341269⟩⟩,⟨⟨1086575322,1528770998⟩,⟨1153081827,2104919066⟩⟩⟩ : FE)+⟨⟨⟨973458266,1691467449⟩,⟨1765941834,1051698078⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨173039117,997531406⟩,⟨1530004149,214770872⟩⟩,⟨⟨693565198,1411725100⟩,⟨145267460,508990992⟩⟩⟩=⟨⟨⟨206822164,239294967⟩,⟨1701938808,1166648691⟩⟩,⟨⟨1926633681,224622122⟩,⟨1395774668,56394308⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs05.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨973458266,1691467449⟩,⟨1765941834,1051698078⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨287584799,1156076550⟩,⟨2035531565,441759647⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs06
end
