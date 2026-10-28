import NDO_JHk_Line01
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs01
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨1064294786,1854137894⟩,⟨696346468,398115270⟩⟩,⟨⟨181923102,1482016283⟩,⟨1144933848,207423094⟩⟩⟩
def power : K := ⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs00.rhs+LiteralOpeningView.eK JHk_Rhs00.power*JHk_Line01.value=rhs := by
  change (⟨⟨⟨693198916,639986381⟩,⟨1864761200,1927747454⟩⟩,⟨⟨2142802787,1648541873⟩,⟨1657099671,1353897268⟩⟩⟩ : FE)+⟨⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨608038418,2035529987⟩,⟨1627580570,1264720253⟩⟩,⟨⟨424887596,1267828159⟩,⟨1951748929,252217331⟩⟩⟩=⟨⟨⟨1064294786,1854137894⟩,⟨696346468,398115270⟩⟩,⟨⟨181923102,1482016283⟩,⟨1144933848,207423094⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs00.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs01
end
