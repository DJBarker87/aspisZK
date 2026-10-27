import FJf_PointFirstCanon
import FJf_RawCircleOuterFrame
import FJf_OriginalFactors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_OriginalCanon
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

theorem source (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) :
    ∀ row,w.factors.val[0]?=some row → FJf_FactorArray.rowCanon row := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hw⟩ :=
    FJc_Constructor.parts v alpha z w run
  have hp0 := FJf_OriginalPoint.value alpha points hp
  have first := FJf_PointFirstCanon.value points alpha hp0 hc _ f1 FJf_FactorZeros.canon hf1
  have frame := FJf_RawCircleOuterFrame.two z 0 (by decide) f1 f2 hf2
  subst w
  intro row hr
  apply first row
  rw [←frame]
  exact hr

theorem installed (v : AspisR1Stage2.transport.Variant)
    (alpha : Array AspisR1Stage2.Stage2Finish.K 10#usize)
    (z : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w)) :
    ∀ row,w.factors.val[0]?=some row → FJf_FactorArray.rowCanon row :=
  source _ _ _ w hc (FJc_Constructor.source v alpha z w run)
#print axioms source
#print axioms installed
end AspisR1.FJf_OriginalCanon
end
