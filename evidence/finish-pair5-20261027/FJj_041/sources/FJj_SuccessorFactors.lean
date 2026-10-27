import FJj_PointSecond
import FJf_ModelPoint
import FJj_SuccessorPoint
import FJf_OriginalFactors
import FJf_RawCircleOuterFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorFactors
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

theorem source (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) :
    (∀ row,w.factors.val[1]?=some row → FJf_FactorArray.rowCanon row) ∧
    ∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 1 d.val s.val=
      FJd_PointReference.pointFactors (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded alpha)) d s := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hw⟩ := FJc_Constructor.parts v alpha z w run
  have hp0 := FJf_OriginalPoint.value alpha points hp
  obtain ⟨successor,hs,cs,vs⟩ := FJj_SuccessorPoint.value alpha points hc hp
  have second := FJj_PointSecond.value points alpha successor hp0 hc hs cs _ f1 FJf_FactorZeros.canon hf1
  have frame := FJf_CircleOuterFrame.two z 1 (by decide) f1 f2 hf2
  have raw := FJf_RawCircleOuterFrame.two z 1 (by decide) f1 f2 hf2
  subst w
  constructor
  · intro row hr
    apply second.1 row
    rw [←raw]
    exact hr
  · intro d s
    rw [frame d.val s.val,second.2 d s,FJf_ModelPoint.factor]
    change FJd_PointReference.pointFactors (FJj_SuccessorStep.decoded successor) d s=_
    rw [vs]
#print axioms source
end AspisR1.FJj_SuccessorFactors
end
