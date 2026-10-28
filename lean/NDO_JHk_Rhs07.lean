import NDO_JHk_Line07
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs07
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨1073200564,1231400400⟩,⟨622391826,253259928⟩⟩,⟨⟨1118867803,70413591⟩,⟨2068958713,807302181⟩⟩⟩
def power : K := ⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs06.rhs+LiteralOpeningView.eK JHk_Rhs06.power*JHk_Line07.value=rhs := by
  change (⟨⟨⟨206822164,239294967⟩,⟨1701938808,1166648691⟩⟩,⟨⟨1926633681,224622122⟩,⟨1395774668,56394308⟩⟩⟩ : FE)+⟨⟨⟨287584799,1156076550⟩,⟨2035531565,441759647⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨321305315,1142875242⟩,⟨10932055,432158760⟩⟩,⟨⟨140563111,1928915987⟩,⟨245305444,1453663545⟩⟩⟩=⟨⟨⟨1073200564,1231400400⟩,⟨622391826,253259928⟩⟩,⟨⟨1118867803,70413591⟩,⟨2068958713,807302181⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs06.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨287584799,1156076550⟩,⟨2035531565,441759647⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs07
end
