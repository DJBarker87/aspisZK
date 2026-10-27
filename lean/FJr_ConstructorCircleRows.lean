import FJr_BeforeCircles
import FJr_CircleRows
import FJc_InstalledParts
import FJj_ArrayReadTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_ConstructorCircleRows
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem value (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) :
    ∃ p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint,
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize=ok p1 ∧
      FJf_FactorArray.canon w.factors ∧
      (∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 3 d.val s.val=
        FJr_CircleOuterCell.digit (FJc_WeightValues.decode p0.x) (FJc_WeightValues.decode p0.y) d.val s) ∧
      (∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 4 d.val s.val=
        FJr_CircleOuterCell.digit (FJc_WeightValues.decode p1.x) (FJc_WeightValues.decode p1.y) d.val s) := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,same⟩ :=
    FJc_Constructor.parts _ _ _ w (FJc_Constructor.source .S2 alpha z w hw)
  have cf1 := FJr_BeforeCircles.value _ points f1 hc hp hf1
  obtain ⟨p0,hp0⟩ := FJj_ArrayReadTotal.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize (by decide)
  obtain ⟨p1,hp1⟩ := FJj_ArrayReadTotal.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize (by decide)
  have rows := FJr_CircleRows.value _ cz p0 p1 hp0 hp1 f1 f2 cf1 hf2
  subst w
  exact ⟨p0,p1,hp0,hp1,rows.1,rows.2.1,rows.2.2⟩

#print axioms value
end AspisR1.FJr_ConstructorCircleRows
end
