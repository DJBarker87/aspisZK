import NDO_JGv_PairShared2
import NDO_JGv_PairSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_Pair
open Aeneas Aeneas.Std Result
open JGq_PairShape
abbrev E := FIo_Install.NE
/-- Complete producing native Pair return on the retained checkpoint/proof tuple. -/
theorem native : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
    w alpha f kappa=ok (.Ok JGv_PairSum.v7) := by
  rw [JGv_PairShared2.native_remaining]
  unfold JGv_PairShared2.remaining
  change (do
    let out ← FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize}
      f JGt_PairWrites.initial JGs_LibraEnd.value
    let sum ← FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize}
      out JGq_PowersK.a7 FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
    ok (core.result.Result.Ok sum)) = _
  rw [JGt_PairWrites.source,bind_tc_ok,JGv_PairSum.source,bind_tc_ok]
#print axioms native
/-- The installed Pair really ran; no successful Pair is an input hypothesis. -/
theorem source : FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
    (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=ok (.Ok JGo_TX2_Horner1_6.after) := by
  have run : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
      (FIo_Install.toWeights JGo_TX2_WeightData.value) (FIo_Install.toSlice JGo_TX2_FinishPrefix.alphas)
      (JFw_Frames.window 8007 2048) (FIo_Install.toE JFo_Prepared.value.kappa)=ok (.Ok JGv_PairSum.v7) := by
    with_unfolding_all exact native
  unfold FIo_Install.pair
  rw [run,bind_tc_ok]
  with_unfolding_all rfl
#print axioms source
end AspisR1.JGv_Pair
end
