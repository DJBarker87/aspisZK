import RPt_JFq_Kappa
import NDO_JHl_Kappa03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Kappa04
abbrev FE := AspisWideTower.WideExact
def value : FE := ⟨⟨⟨2006370403,841359646⟩,⟨376899686,2013808952⟩⟩,⟨⟨1241193111,1543519322⟩,⟨400137173,1242945666⟩⟩⟩
/-- One bounded exact field multiplication for the remaining prepared claim. -/
theorem step : JHl_Kappa03.value*CheckpointBytes5Output.ofE JFq_Kappa.scalar=value := by
  change (⟨⟨⟨1266306440,1524792638⟩,⟨36588852,1044096672⟩⟩,⟨⟨2018106446,381171209⟩,⟨1489892152,1479239577⟩⟩⟩ : FE)*⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩=⟨⟨⟨2006370403,841359646⟩,⟨376899686,2013808952⟩⟩,⟨⟨1241193111,1543519322⟩,⟨400137173,1242945666⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : CheckpointBytes5Output.ofE JFq_Kappa.scalar^4=value := by
  rw [pow_succ,JHl_Kappa03.source,step]
#print axioms source
end AspisR1.JHl_Kappa04
end
