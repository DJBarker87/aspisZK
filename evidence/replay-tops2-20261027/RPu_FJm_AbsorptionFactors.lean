import RPu_FJm_PointThird
import RPu_FJm_AbsorptionPoint
import RPu_FJf_ModelPoint
import RPu_FJj_SuccessorPoint
import RPu_FJf_OriginalFactors
import RPu_FJf_RawCircleOuterFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionFactors
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

theorem source (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) :
    (∀ row,w.factors.val[2]?=some row → FJf_FactorArray.rowCanon row) ∧
    ∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 2 d.val s.val=
      FJd_PointReference.pointFactors (R0P.SemSource.xor12Point (FJf_ModelPoint.decoded alpha)) d s := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hw⟩ := FJc_Constructor.parts v alpha z w run
  have hp0 := FJf_OriginalPoint.value alpha points hp
  obtain ⟨successor,hs,cs,vs⟩ := FJj_SuccessorPoint.value alpha points hc hp
  obtain ⟨absorption,ha,ca,va⟩ := FJm_AbsorptionPoint.value alpha points hc hp
  have third := FJm_PointThird.value points alpha successor absorption hp0 hc hs cs ha ca _ f1 FJf_FactorZeros.canon hf1
  have frame := FJf_CircleOuterFrame.two z 2 (by decide) f1 f2 hf2
  have raw := FJf_RawCircleOuterFrame.two z 2 (by decide) f1 f2 hf2
  subst w
  constructor
  · intro row hr
    apply third.1 row
    rw [←raw]
    exact hr
  · intro d s
    rw [frame d.val s.val,third.2 d s,FJf_ModelPoint.factor]
    change FJd_PointReference.pointFactors (FJf_ModelPoint.decoded absorption) d s=_
    rw [va]
#print axioms source
end AspisR1.FJm_AbsorptionFactors
end
