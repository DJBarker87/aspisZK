import RPu_FJr_TraceRegularCanonical
import RPu_FJr_SharedCanonical
import RPu_FJr_LibraArrayCanonical
import RPu_FJf_CommonValue
import RPu_FJg_PartialsValue
import RPu_FJm_LibraCanonical
import RPu_FJm_ExtraCanon
import RPu_FJc_LowPowers
import RPu_FGm_GroupDispatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_TracePartsCanonical
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
    (len : f.val.length=2048) (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    letI := FIo_Install.allocation r;
    FIo_ArrayCanon.Holds t.parts := by
  letI := FIo_Install.allocation r
  have ca0 := FJc_SliceCanonical.read alpha 0#usize t.a0 halpha t.read0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize t.a1 halpha t.read1
  have cp0 := (FIp_PowersValue.powers 4#usize t.a0 t.ap0 ca0 t.powers0).1
  have cp1 := (FIp_PowersValue.powers 4#usize t.a1 t.ap1 ca1 t.powers1).1
  obtain ⟨point0,point1,hz0,hz1,cf,vf0,vf1⟩ := FJr_ConstructorCircleRows.value semAlpha z w hc cz hw
  have regular := FJr_TraceRegularCanonical.value r semAlpha z w hc cz hw alpha f kappa out t halpha
  have cv := FJf_CommonValue.sixteen semAlpha z w hc hw (_,t.common) t.commonRun
  have pv := FJg_PartialsValue.four f t.common cv.2.1 t.commonPartials t.partialsRun
  have shared := FJr_SharedCanonical.value w cf t.commonPartials t.ap0 t.ap1 pv.1 cp0 cp1
    t.regularParts t.sharedParts regular t.sharedRun
  have low := FJc_LowPowers.value t.a0 t.a1 t.ap0 t.ap1 t.low ca0 ca1 t.powers0 t.powers1 t.lowRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  have inactiveRun := t.inactiveRun
  rw [FGm_GroupDispatch.same (FIo_Install.toWeights w) f t.low variantS2 len] at inactiveRun
  have inactive := FIo_GroupCanonical.canonical f t.low t.inactive low.1 inactiveRun
  have lowParts := FIo_ArrayCanon.update t.sharedParts t.lowParts 0#usize t.inactive shared inactive t.inactiveWrite
  have extra := FJm_ExtraCanon.value semAlpha z w hc hw
  have libra := FJm_LibraCanonical.value t.ap0 t.ap1 (FIo_Install.toWeights w).extra t.libra cp0 cp1 extra t.libraRun
  exact FJr_LibraArrayCanonical.value f t.libra libra _ t.lowParts t.parts lowParts t.libraWrite

#print axioms value
end AspisR1.FJr_TracePartsCanonical
end
