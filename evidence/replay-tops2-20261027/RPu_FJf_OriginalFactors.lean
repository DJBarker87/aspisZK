import RPu_FJf_PointFirst
import RPu_FJf_OriginalPoint
import RPu_FJf_CircleOuterFrame
import RPu_FJf_FactorZeros
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_OriginalFactors
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

theorem source (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) :
    ∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 0 d.val s.val=
      FJf_PointCell.point alpha d.val s := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hw⟩ :=
    FJc_Constructor.parts v alpha z w run
  have hp0 := FJf_OriginalPoint.value alpha points hp
  have first := FJf_PointFirst.value points alpha hp0 hc _ f1 FJf_FactorZeros.canon hf1
  have frame := FJf_CircleOuterFrame.two z 0 (by decide) f1 f2 hf2
  subst w
  intro d s
  exact (frame d.val s.val).trans (first d s)

/-- Same installed constructor operands; only their input canonicality remains
local. This is a constructor factor VALUE, not a complete Pair part meaning. -/
theorem installed (v : AspisR1Stage2.transport.Variant)
    (alpha : Aeneas.Std.Array AspisR1Stage2.Stage2Finish.K 10#usize)
    (z : Aeneas.Std.Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w)) :
    ∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 0 d.val s.val=
      FJf_PointCell.point (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) d.val s :=
  source _ _ _ w hc (FJc_Constructor.source v alpha z w run)
#print axioms source
#print axioms installed
end AspisR1.FJf_OriginalFactors
end
