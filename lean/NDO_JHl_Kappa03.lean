import RPt_JFq_Kappa
import NDO_JHl_Kappa02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Kappa03
abbrev FE := AspisWideTower.WideExact
def value : FE := ⟨⟨⟨1266306440,1524792638⟩,⟨36588852,1044096672⟩⟩,⟨⟨2018106446,381171209⟩,⟨1489892152,1479239577⟩⟩⟩
/-- One bounded exact field multiplication for the remaining prepared claim. -/
theorem step : JHl_Kappa02.value*CheckpointBytes5Output.ofE JFq_Kappa.scalar=value := by
  change (⟨⟨⟨194086607,1888419081⟩,⟨1301861674,1187144623⟩⟩,⟨⟨855257644,590989944⟩,⟨1958695353,1064062444⟩⟩⟩ : FE)*⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩=⟨⟨⟨1266306440,1524792638⟩,⟨36588852,1044096672⟩⟩,⟨⟨2018106446,381171209⟩,⟨1489892152,1479239577⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : CheckpointBytes5Output.ofE JFq_Kappa.scalar^3=value := by
  rw [pow_succ,JHl_Kappa02.source,step]
#print axioms source
end AspisR1.JHl_Kappa03
end
