import NDO_JHk_Line04
import RPt_JFq_Rho
import RPt_JFq_Rhs
import NDO_JHk_Rhs03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs04
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨1912763292,1473059900⟩,⟨1095070407,756137035⟩⟩,⟨⟨279988608,201928833⟩,⟨1764268037,240284230⟩⟩⟩
def power : K := ⟨⟨741587425,1272351995⟩,⟨1232633493,701380605⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : JHk_Rhs03.rhs+LiteralOpeningView.eK JHk_Rhs03.power*JHk_Line04.value=rhs := by
  change (⟨⟨⟨338728416,53922787⟩,⟨156546995,1798905091⟩⟩,⟨⟨41624832,159719658⟩,⟨682142995,1144834632⟩⟩⟩ : FE)+⟨⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩*⟨⟨⟨1756724545,1716894538⟩,⟨747245482,1119058880⟩⟩,⟨⟨342240434,2099954053⟩,⟨1915563436,734053244⟩⟩⟩=⟨⟨⟨1912763292,1473059900⟩,⟨1095070407,756137035⟩⟩,⟨⟨279988608,201928833⟩,⟨1764268037,240284230⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms rhs_step
theorem power_step : JHk_Rhs03.power*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  change (⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩ : K)*⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨741587425,1272351995⟩,⟨1232633493,701380605⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms power_step
end AspisR1.JHk_Rhs04
end
