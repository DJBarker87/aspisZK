import NDO_JGx_Ranges
import NDO_JGx_Writeback
import NDO_JGo_TX2_FinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Tail
open Aeneas Aeneas.Std Result AspisR1Stage2
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

theorem source (ops : VTop_Stages.Ops) (inactive : aspis_core.field.wide_exact.WideExact)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (flushed : Slice aspis_core.field.QM31)
    (flush : ops.op9 b a.weights.deref=ok flushed)
    (offset1 : ops.op21=ok 8007#usize) (offset2 : ops.op20=ok 10055#usize)
    (finish : ops.op19 (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value
      (JGx_Writeback.value a flushed) none=ok (.Ok ())) :
    Tx2I_Cuts.tail ops JFx_NativeBytes.proof JFo_Prepared.value none inactive
      7527#usize 7751#usize 7783#usize (a,b)=ok (.Ok ()) := by
  unfold Tx2I_Cuts.tail
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry]
  have actualFlush : ops.op9 b (alloc.vec.Vec.deref_mut a.weights).1=ok flushed := flush
  rw [actualFlush,bind_tc_ok]
  rw [JGx_Ranges.round0,bind_tc_ok,offset1,bind_tc_ok,JGx_Ranges.round1,bind_tc_ok,
    offset2,bind_tc_ok,JGx_Ranges.final_message,bind_tc_ok]
  exact finish
#print axioms source
end AspisR1.JGx_Tail
end
