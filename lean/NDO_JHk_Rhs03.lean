import NDO_JHk_Line03
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs03
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨338728416,53922787⟩,⟨156546995,1798905091⟩⟩,⟨⟨41624832,159719658⟩,⟨682142995,1144834632⟩⟩⟩
def power : K := ⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs02.rhs+LiteralOpeningView.eK JHk_Rhs02.power*JHk_Line03.value=rhs := by
  change (⟨⟨⟨586725044,1602006507⟩,⟨771566795,604716937⟩⟩,⟨⟨432446998,375155712⟩,⟨847844395,577105035⟩⟩⟩ : FE)+⟨⟨⟨1658013629,1794986150⟩,⟨428892014,637833112⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨1486385033,641769127⟩,⟨268612740,885452757⟩⟩,⟨⟨2147418281,2102404536⟩,⟨1140985490,77746572⟩⟩⟩=⟨⟨⟨338728416,53922787⟩,⟨156546995,1798905091⟩⟩,⟨⟨41624832,159719658⟩,⟨682142995,1144834632⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs02.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨1658013629,1794986150⟩,⟨428892014,637833112⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs03
end
