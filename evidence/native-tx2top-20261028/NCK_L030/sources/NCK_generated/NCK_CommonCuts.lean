import VTop_SecondFlow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_CommonCuts
open Aeneas Aeneas.Std Result VTop_Stages
/-- Forward VALUE composition of the actual TX2 orchestration prefix.
These are local model call equations, not native lower-unit bridges. The
unreplaced tail still flushes the SAME pending accumulator and builds the
actual relation view. No oracle-history or native acceptance claim is made. -/
theorem compose (ops : VTop_Stages.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (pub proof cp : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (inactive : aspis_core.field.wide_exact.WideExact)
    (optionInactive : Option aspis_core.field.wide_exact.WideExact)
    (inactiveStart round0 folded round1 : Usize)
    (inactiveBytes foldedBytes : Slice U8) (root : Array U8 32#usize)
    (converted : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (returned : verifier.Accumulator × verifier.BatchedWeights)
    (resumeCut : ops.op18 D cp proof pub .S2 hash = ok (.Ok (p,a)))
    (splitCut : ops.op16 = ok 10#usize) (nextTen : a.next = 10#usize)
    (powersCut : ops.op17 29#usize p.gamma = ok g)
    (markRead : ops.op13 none _root_.AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead = ok ())
    (inactiveOffset : ops.op23 = ok inactiveStart) (round0Offset : ops.op22 = ok round0)
    (inactiveRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := inactiveStart, «end» := round0} = ok inactiveBytes)
    (decodeInactive : ops.op2 inactiveBytes = ok optionInactive)
    (checkInactive : ops.op0 optionInactive _root_.AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse = ok (.Ok inactive))
    (foldedOffset : ops.op15 = ok folded) (round1Offset : ops.op14 = ok round1)
    (foldedRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := folded, «end» := round1} = ok foldedBytes)
    (convertRoot : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 foldedBytes = ok converted)
    (unwrapRoot : ops.unwrap32 converted = ok root)
    (batchCut : ops.op5 D proof p root 1#usize hash = ok (.Ok ()))
    (markBatch : ops.op13 none (_root_.AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle 10#usize) = ok ())
    (geometryCut : ops.op11 p.queries a.next 22#usize = ok (.Ok geometry))
    (pendingCut : ops.op10 a.weights.deref = ok (.Ok pending))
    (queryCut : ops.op6 proof p a g none geometry pending 22#usize = ok (.Ok returned))
    (tailCut : VTop_SecondFlow.tail (VTop_Flow.sourceEffects ops) proof p none
      inactive round0 folded round1 returned = ok (.Ok ())) :
    verifier.candidate.tx2_common ops D pub proof cp hash none = ok (.Ok ()) := by
  change VTop_SecondFlow.common (VTop_Flow.sourceEffects ops) D pub proof cp hash none = _
  simp only [VTop_SecondFlow.common, VTop_Flow.sourceEffects, resumeCut,
    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, splitCut,
    nextTen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    powersCut, markRead, inactiveOffset, round0Offset, inactiveRange,
    decodeInactive, checkInactive, foldedOffset, round1Offset, foldedRange,
    convertRoot, unwrapRoot, batchCut, markBatch, geometryCut, pendingCut, queryCut, tailCut]
#print axioms compose
end AspisR1.NCK_CommonCuts
end
