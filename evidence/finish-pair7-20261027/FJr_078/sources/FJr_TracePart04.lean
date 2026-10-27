import FJr_PairTrace
import FJr_InactiveMeaning
import FJr_LibraMeaning
import FJr_ExtraValue
import FJc_LowPowers
import FJc_SliceCanonical
import FJm_ExtraCanon
import FGm_GroupDispatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_TracePart04
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (t : @FJr_PairTrace.Trace (FIo_Install.allocation r) (FIo_Install.toWeights w) alpha f kappa out)
    (len : f.val.length=2048) (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    letI := FIo_Install.allocation r;
    FIp_ArrayValue.value t.parts 0=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0)) FJr_InactiveRaw.raw)) ∧
    FIp_ArrayValue.value t.parts 4=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (FJm_LibraModel.folded (algebraMap FK FE (FJc_WeightArray.value
        (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) 8))
        (algebraMap FK FE (FJc_WeightArray.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) 9))
        (decodeWide (wide t.a0)) (decodeWide (wide t.a1))) := by
  letI := FIo_Install.allocation r
  have ca0 := FJc_SliceCanonical.read alpha 0#usize t.a0 halpha t.read0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize t.a1 halpha t.read1
  have low := FJc_LowPowers.value t.a0 t.a1 t.ap0 t.ap1 t.low ca0 ca1 t.powers0 t.powers1 t.lowRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  have inactiveRun := t.inactiveRun
  rw [FGm_GroupDispatch.same (FIo_Install.toWeights w) f t.low variantS2 len] at inactiveRun
  have vi := FJc_InactiveValue.value f t.low t.inactive low.1 inactiveRun
  have inactive := FJr_InactiveMeaning.value f t.low (decodeWide (wide t.a0)) (decodeWide (wide t.a1)) low.2
  have frame := FJc_LibraFrame.value f t.libra t.lowParts t.parts _ t.libraWrite 0 (by decide)
  have extra := FJm_ExtraCanon.value semAlpha z w hc hw
  have libra := FJr_LibraMeaning.value t.a0 t.a1 t.ap0 t.ap1 t.libra (FIo_Install.toWeights w).extra
    ca0 ca1 t.powers0 t.powers1 extra t.libraRun f t.lowParts t.parts t.libraZero t.libraWrite
  have ev := FJr_ExtraValue.value semAlpha z w hw
  rw [ev.1,ev.2] at libra
  refine ⟨?_,libra⟩
  rw [frame,FJc_ArrayUpdateValue.value t.sharedParts t.lowParts 0#usize t.inactive 0 t.inactiveWrite,
    if_pos (by rfl),vi.2,inactive]

#print axioms value
end AspisR1.FJr_TracePart04
end
