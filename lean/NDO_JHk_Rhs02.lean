import NDO_JHk_Line02
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs02
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨586725044,1602006507⟩,⟨771566795,604716937⟩⟩,⟨⟨432446998,375155712⟩,⟨847844395,577105035⟩⟩⟩
def power : K := ⟨⟨1658013629,1794986150⟩,⟨428892014,637833112⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs01.rhs+LiteralOpeningView.eK JHk_Rhs01.power*JHk_Line02.value=rhs := by
  change (⟨⟨⟨1064294786,1854137894⟩,⟨696346468,398115270⟩⟩,⟨⟨181923102,1482016283⟩,⟨1144933848,207423094⟩⟩⟩ : FE)+⟨⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨668638683,1399516972⟩,⟨200659360,1745853467⟩⟩,⟨⟨1247716643,559966262⟩,⟨376459622,998644509⟩⟩⟩=⟨⟨⟨586725044,1602006507⟩,⟨771566795,604716937⟩⟩,⟨⟨432446998,375155712⟩,⟨847844395,577105035⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs01.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨1658013629,1794986150⟩,⟨428892014,637833112⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs02
end
