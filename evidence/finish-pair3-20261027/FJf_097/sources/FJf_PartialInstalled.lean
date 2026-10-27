import FJf_PartialValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PartialInstalled
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)

/-- Local composition on SAME installed weights, shared tensor and message.
The two call observations still have to be obtained from the enclosing Pair. -/
theorem value (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (nativeSelf : FIo_Native.weights.Weights) (common : Array NQ 16#usize)
    (hcommon : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (FIo_Install.toWeights w) (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (nativeSelf,common))
    (f : Slice U8) (s : Usize) (hs : s.val < 4) (out : NE)
    (hpartial : FIo_Native.weights.partial_dot f common s=ok (.Ok out)) :
    nativeSelf=FIo_Install.toWeights w ∧ FJf_QMArray.canon common ∧
    (∀ j,j < 16 → FJf_QMArray.value common j=
      FJf_CommonCell.model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) j) ∧
    FIo_WideValues.Canon out ∧ AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide out)=
      FJf_PartialCell.sumPrefix f common s 16 := by
  obtain ⟨same,canon,values⟩ := FJf_CommonValue.sixteen alpha z w hc hw (nativeSelf,common) hcommon
  have partialValue := FJf_PartialValue.sixteen f common s hs canon out hpartial
  exact ⟨same,canon,values,partialValue.1,partialValue.2⟩
#print axioms value
end AspisR1.FJf_PartialInstalled
end
