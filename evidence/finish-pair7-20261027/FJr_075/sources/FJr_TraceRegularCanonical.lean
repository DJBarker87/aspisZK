import FJr_PairTrace
import FJr_RegularCanonical
import FJr_KindTwoCanonical
import FJr_KindIndices
import FJr_ConstructorCircleRows
import FJr_NativeRow
import FJm_Filled
import FJc_SliceCanonical
import FIp_PowersValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_TraceRegularCanonical
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ)

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (t : @FJr_PairTrace.Trace (FIo_Install.allocation r) (FIo_Install.toWeights w) alpha f kappa out)
    (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    FIo_ArrayCanon.Holds t.regularParts := by
  letI := FIo_Install.allocation r
  have ca0 := FJc_SliceCanonical.read alpha 0#usize t.a0 halpha t.read0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize t.a1 halpha t.read1
  have cp0 := (FIp_PowersValue.powers 4#usize t.a0 t.ap0 ca0 t.powers0).1
  have cp1 := (FIp_PowersValue.powers 4#usize t.a1 t.ap1 ca1 t.powers1).1
  obtain ⟨point0,point1,hz0,hz1,cf,vf0,vf1⟩ := FJr_ConstructorCircleRows.value semAlpha z w hc cz hw
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  obtain ⟨row1,hr1⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 1#usize (by decide)
  obtain ⟨row3,hr3⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 3#usize (by decide)
  obtain ⟨row4,hr4⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 4#usize (by decide)
  have c1 := (FJr_NativeRow.value w cf 1#usize row1 hr1).1
  have c3 := (FJr_NativeRow.value w cf 3#usize row3 hr3).1
  have c4 := (FJr_NativeRow.value w cf 4#usize row4 hr4).1
  have cs := FJm_Filled.canonical r 64#usize t.scratch t.filled
  obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := FJj_RegularTrace.reached (FIo_Install.toWeights w)
    alpha f 2#usize 64#usize t.ap0 t.ap1 t.scratch t.scratchOut _ t.regularParts t.regular
  have v2 := FJr_KindTwoCanonical.value (FIo_Install.toWeights w) variant row1 hr1 c1 alpha f t.ap0 t.ap1
    cp0 cp1 t.scratch s1 _ p1 cs (FIo_GroupCanonical.zeros _) h2
  have v5 := FJr_RegularCanonical.value (FIo_Install.toWeights w) variant 5#usize 3#usize (by decide)
    FJr_KindIndices.five row3 hr3 c3 alpha f t.ap0 t.ap1 cp0 cp1 s1 s2 p1 p2 v2.1 v2.2 h5
  have v6 := FJr_RegularCanonical.value (FIo_Install.toWeights w) variant 6#usize 4#usize (by decide)
    FJr_KindIndices.six row4 hr4 c4 alpha f t.ap0 t.ap1 cp0 cp1 s2 t.scratchOut p2 t.regularParts v5.1 v5.2 h6
  exact v6.2

#print axioms value
end AspisR1.FJr_TraceRegularCanonical
end
