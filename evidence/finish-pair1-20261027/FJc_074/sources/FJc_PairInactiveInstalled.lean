import FJc_PairInactiveValue
import FJc_InstalledParts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_PairInactiveInstalled
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE)
/-- Same installed constructor AND same installed Pair. Local length and
canonicality conditions remain explicit; no model Pair conclusion is assumed. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut inactive : NE) (low : Array NE 16#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      FIo_Native.weights.grouped_inactive_pair (FIo_Install.toWeights w) f low=ok inactive ∧
      FIo_ArrayCanon.Holds low ∧ FIo_WideValues.Canon inactive ∧
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide inactive)=FJc_InactiveValue.sumPrefix f low 12 := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hvariant,rest⟩ :=
    FJc_InstalledParts.value .S2 semAlpha z w hw
  have variant : (FIo_Install.toWeights w).variant=.S2 := hvariant
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨a0,a1,ap0,ap1,low,inactive,h0,hp0,h1,hp1,hl,hi,hc,ci,vi,vl⟩ :=
    @FJc_PairInactiveValue.value (FIo_Install.allocation r) (FIo_Install.toWeights w)
      (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut folds variant len halpha hn
  exact ⟨nativeOut,inactive,low,hn,he,hi,hc,ci,vi⟩
#print axioms value
end AspisR1.FJc_PairInactiveInstalled
end
