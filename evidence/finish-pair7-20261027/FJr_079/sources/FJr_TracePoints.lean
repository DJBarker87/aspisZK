import FJr_PairTrace
import FJj_Part1Meaning
import FJm_Part2Meaning
import FJm_Part3Meaning
import FJg_SharedPart1
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_TracePoints
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (t : @FJr_PairTrace.Trace (FIo_Install.allocation r) (FIo_Install.toWeights w) alpha f kappa out)
    (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    letI := FIo_Install.allocation r;
    FIp_ArrayValue.value t.parts 1=RoundPairing.dot (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
          (fun j=>algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha)) j)))) ∧
    FIp_ArrayValue.value t.parts 2=RoundPairing.dot (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
          (fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j)))) ∧
    FIp_ArrayValue.value t.parts 3=RoundPairing.dot (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
          (fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.xor12Point (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j)))) := by
  letI := FIo_Install.allocation r
  have ca0 := FJc_SliceCanonical.read alpha 0#usize t.a0 halpha t.read0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize t.a1 halpha t.read1
  have cp0 := (FIp_PowersValue.powers 4#usize t.a0 t.ap0 ca0 t.powers0).1
  have cp1 := (FIp_PowersValue.powers 4#usize t.a1 t.ap1 ca1 t.powers1).1
  have cv := FJf_CommonValue.sixteen semAlpha z w hc hw (_,t.common) t.commonRun
  have pv := FJg_PartialsValue.four f t.common cv.2.1 t.commonPartials t.partialsRun
  obtain ⟨row,coeff,low0,low1,hr,hd4,hd0,hd1,v1⟩ := FJg_SharedPart1.value semAlpha z w hc hw
    t.commonPartials t.ap0 t.ap1 pv.1 cp0 cp1 t.regularParts t.sharedParts t.sharedRun
  have scale0 := FJj_ScaleModel.value semAlpha z w hc hw 0 row low0 hr hd0 t.a0 t.ap0 ca0 t.powers0
  have scale1 := FJj_ScaleModel.value semAlpha z w hc hw 1 row low1 hr hd1 t.a1 t.ap1 ca1 t.powers1
  have high := FJj_HighReference.value semAlpha z w hc hw f t.common t.commonPartials cv.2.2 pv.2 row coeff hr hd4
  have shared1 : FIp_ArrayValue.value t.sharedParts 1=RoundPairing.dot (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
          (fun j=>algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha)) j)))) := by
    rw [v1,scale0,scale1,high]
    have tensor : (fun j=>algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha)) j))=
        FJd_PointReference.tensor (FJg_LiteralTensor.factors semAlpha) := by
      funext j
      exact (FJg_LiteralTensor.value semAlpha j).symm
    rw [tensor,RoundPairing.dot]
    simp_rw [FJg_DualTensor.value]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have cs := FJm_Filled.canonical r 64#usize t.scratch t.filled
  obtain ⟨s1,p1,h2,carry2⟩ := FJm_RegularContinuation.value (FIo_Install.toWeights w)
    alpha f 2#usize 64#usize t.ap0 t.ap1 t.scratch t.scratchOut _ t.regularParts t.regular
  have v2 := FJm_KindTwoMeaning.value r semAlpha z w hc hw alpha f t.a0 t.a1 t.ap0 t.ap1
    ca0 ca1 t.powers0 t.powers1 t.scratch s1 _ p1 cs h2
  have shared2 := FJm_Continuation.shared (FIo_Install.toWeights w) t.commonPartials t.ap0 t.ap1
    t.regularParts t.sharedParts t.sharedRun 2 (by decide) (by decide)
  have shared3 := FJm_AbsorptionMeaning.value semAlpha z w hc hw f t.common t.commonPartials cv.2.2 pv.2 pv.1
    t.a0 t.a1 t.ap0 t.ap1 ca0 ca1 t.powers0 t.powers1 t.regularParts t.sharedParts t.sharedRun
  have tail1 := FJm_Continuation.tail f t.libra t.sharedParts t.lowParts t.parts t.inactive t.inactiveWrite t.libraWrite 1 (by decide) (by decide)
  have tail2 := FJm_Continuation.tail f t.libra t.sharedParts t.lowParts t.parts t.inactive t.inactiveWrite t.libraWrite 2 (by decide) (by decide)
  have tail3 := FJm_Continuation.tail f t.libra t.sharedParts t.lowParts t.parts t.inactive t.inactiveWrite t.libraWrite 3 (by decide) (by decide)
  exact ⟨tail1.trans shared1,tail2.trans (shared2.trans (carry2.trans v2)),tail3.trans shared3⟩

#print axioms value
end AspisR1.FJr_TracePoints
end
