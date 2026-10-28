import NDO_JFn_Accumulate
import NDO_JFn_Flush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_AccumulationFlush
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The first actual accumulation from the decoded checkpoint also has a
returning installed flush. The supplied node/value have not been identified
with the query's geometry/folding results, so this is not query acceptance. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (node : U32) (value : SAQ_WideABI.E)
    (canonical : Port4C_QueryArithmetic.CanonE value) :
    ∃ out after flushed,
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
        JFo_Prepared.value JFo_Prepared.accumulator node value JFo_Pending.value=ok (out,after) ∧
      out.weights=JFo_Prepared.accumulator.weights ∧ out.next=11#usize ∧
      Port3_FlushInstall.flush after out.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q := by
  obtain ⟨out,after,run,weights,next,_,_,length⟩ := JFn_Accumulate.source seed node value canonical
  obtain ⟨flushed,flush,size,canon⟩ := JFn_Flush.source after length
  exact ⟨out,after,flushed,run,weights,next,by rw [weights];exact flush,size,canon⟩

#print axioms source
end AspisR1.JFn_AccumulationFlush
end
