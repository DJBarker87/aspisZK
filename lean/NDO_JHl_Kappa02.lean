import RPt_JFq_Kappa
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Kappa02
abbrev FE := AspisWideTower.WideExact
def value : FE := ⟨⟨⟨194086607,1888419081⟩,⟨1301861674,1187144623⟩⟩,⟨⟨855257644,590989944⟩,⟨1958695353,1064062444⟩⟩⟩
/-- One bounded exact field multiplication for the remaining prepared claim. -/
theorem step : CheckpointBytes5Output.ofE JFq_Kappa.scalar*CheckpointBytes5Output.ofE JFq_Kappa.scalar=value := by
  change (⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩ : FE)*⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩=⟨⟨⟨194086607,1888419081⟩,⟨1301861674,1187144623⟩⟩,⟨⟨855257644,590989944⟩,⟨1958695353,1064062444⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : CheckpointBytes5Output.ofE JFq_Kappa.scalar^2=value := by
  rw [pow_two]
  exact step
#print axioms source
end AspisR1.JHl_Kappa02
end
