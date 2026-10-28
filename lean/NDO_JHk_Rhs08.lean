import NDO_JHk_Line08
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs08
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨1609915618,1406937229⟩,⟨1284218296,550047463⟩⟩,⟨⟨1722769472,1118979547⟩,⟨444162423,1656256757⟩⟩⟩
def power : K := ⟨⟨160410907,665703601⟩,⟨1363748181,807933172⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs07.rhs+LiteralOpeningView.eK JHk_Rhs07.power*JHk_Line08.value=rhs := by
  change (⟨⟨⟨1073200564,1231400400⟩,⟨622391826,253259928⟩⟩,⟨⟨1118867803,70413591⟩,⟨2068958713,807302181⟩⟩⟩ : FE)+⟨⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨313131969,1815705108⟩,⟨150686342,1526262263⟩⟩,⟨⟨610612430,571614974⟩,⟨1765356495,1775372326⟩⟩⟩=⟨⟨⟨1609915618,1406937229⟩,⟨1284218296,550047463⟩⟩,⟨⟨1722769472,1118979547⟩,⟨444162423,1656256757⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs07.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨160410907,665703601⟩,⟨1363748181,807933172⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs08
end
