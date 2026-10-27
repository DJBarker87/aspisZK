import RPt_FJc_InstalledParts
import RPt_FJc_WeightArray
import RPv_FJj_QMSlice
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_ExtraCanon
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)

theorem value (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (run : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) :
    ∀ q∈(FIo_Install.toWeights w).extra.val,FIo_QMValues.Canon q := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,variant,pointsEq,extraEq,factorsEq⟩ :=
    FJc_InstalledParts.value .S2 alpha z w run
  have c8 := FJc_WeightArray.canonical_read _ 8#usize a8 hc h8
  have c9 := FJc_WeightArray.canonical_read _ 9#usize a9 hc h9
  rw [extraEq]
  intro q hq
  change q∈[FIo_Install.toQ a8,FIo_Install.toQ a9] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl
  · exact c8
  · exact c9
#print axioms value
end AspisR1.FJm_ExtraCanon
end
