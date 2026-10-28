import RPt_JFq_Kappa
import NDO_JHl_Kappa04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Kappa05
abbrev FE := AspisWideTower.WideExact
def value : FE := ⟨⟨⟨1376226683,1712321640⟩,⟨190663200,1810133619⟩⟩,⟨⟨1051832243,1950132196⟩,⟨483065632,20684665⟩⟩⟩
/-- One bounded exact field multiplication for the remaining prepared claim. -/
theorem step : JHl_Kappa04.value*CheckpointBytes5Output.ofE JFq_Kappa.scalar=value := by
  change (⟨⟨⟨2006370403,841359646⟩,⟨376899686,2013808952⟩⟩,⟨⟨1241193111,1543519322⟩,⟨400137173,1242945666⟩⟩⟩ : FE)*⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩=⟨⟨⟨1376226683,1712321640⟩,⟨190663200,1810133619⟩⟩,⟨⟨1051832243,1950132196⟩,⟨483065632,20684665⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : CheckpointBytes5Output.ofE JFq_Kappa.scalar^5=value := by
  rw [pow_succ,JHl_Kappa04.source,step]
#print axioms source
end AspisR1.JHl_Kappa05
end
