import RPv_FJr_TracePart04
import RPv_FJr_TracePoints
import RPv_FJr_TraceCircles
import RPv_FJr_TracePartsCanonical
import RPu_FJr_PairRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_PairParts
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (t : @FJr_PairTrace.Trace (FIo_Install.allocation r) (FIo_Install.toWeights w) alpha f kappa out)
    (len : f.val.length=2048) (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    letI := FIo_Install.allocation r;
    ∃ p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint,
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize=ok p1 ∧
      FIo_ArrayCanon.Holds t.parts ∧ ∀ j : Fin 7,
        FIp_ArrayValue.value t.parts j.val=RoundPairing.dot
          (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
          (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
            (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0)) (FJr_PairRows.rows semAlpha p0 p1 j))) := by
  letI := FIo_Install.allocation r
  have p04 := FJr_TracePart04.value r semAlpha z w hc hw alpha f kappa out t len halpha
  have points := FJr_TracePoints.value r semAlpha z w hc hw alpha f kappa out t halpha
  obtain ⟨p0,p1,hz0,hz1,v5,v6⟩ := FJr_TraceCircles.value r semAlpha z w hc cz hw alpha f kappa out t halpha
  have canon := FJr_TracePartsCanonical.value r semAlpha z w hc cz hw alpha f kappa out t len halpha
  refine ⟨p0,p1,hz0,hz1,canon,?_⟩
  intro j
  fin_cases j
  · exact p04.1
  · exact points.1
  · exact points.2.1
  · exact points.2.2
  · exact p04.2
  · exact v5
  · exact v6

#print axioms value
end AspisR1.FJr_PairParts
end
