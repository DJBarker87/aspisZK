import RPu_FJr_PointAllCanon
import RPu_FJj_SuccessorPoint
import RPu_FJm_AbsorptionPoint
import RPu_FJf_OriginalPoint
import RPu_FJf_FactorZeros
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_BeforeCircles
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJf_PointBody (Points Factors)

theorem value (alpha : Array SQ 10#usize) (points : Points) (out : Factors)
    (hc : FJc_WeightArray.canonical alpha)
    (hp : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points)
    (run : FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize}
      points FJf_FactorZeros.zeros=ok out) : FJf_FactorArray.canon out := by
  have hp0 := FJf_OriginalPoint.value alpha points hp
  obtain ⟨p1,hp1,hc1,v1⟩ := FJj_SuccessorPoint.value alpha points hc hp
  obtain ⟨p2,hp2,hc2,v2⟩ := FJm_AbsorptionPoint.value alpha points hc hp
  exact FJr_PointAllCanon.value points alpha p1 p2 hp0 hc hp1 hc1 hp2 hc2
    FJf_FactorZeros.zeros out FJf_FactorZeros.canon run

#print axioms value
end AspisR1.FJr_BeforeCircles
end
