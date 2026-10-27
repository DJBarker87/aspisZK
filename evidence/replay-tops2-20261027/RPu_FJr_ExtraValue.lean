import RPt_FJc_InstalledParts
import RPt_FJc_WeightArray
import RPu_FJf_QMArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_ExtraValue
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem value (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W) (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) :
    FJf_QMArray.value (FIo_Install.toWeights w).extra 0=
      FJc_WeightArray.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) 8 ∧
    FJf_QMArray.value (FIo_Install.toWeights w).extra 1=
      FJc_WeightArray.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) 9 := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,variant,pointsEq,extraEq,factorsEq⟩ :=
    FJc_InstalledParts.value .S2 alpha z w hw
  rw [extraEq]
  constructor
  · change FJc_WeightValues.decode a8=FJc_WeightArray.value _ 8
    exact (FJc_WeightArray.read _ 8#usize a8 h8).symm
  · change FJc_WeightValues.decode a9=FJc_WeightArray.value _ 9
    exact (FJc_WeightArray.read _ 9#usize a9 h9).symm

#print axioms value
end AspisR1.FJr_ExtraValue
end
