import NDO_JGx_FinishAfterPair
import NDO_JGx_DotGate
import NDO_JGx_FinishDot
import NDO_JGx_Writeback
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Finish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (query : Port3_NativeQueryBody.Ops) (seed : FinishOps FIo_Install.W) (inactive : E)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (flushed : Slice K)
    (updates : JFz_TX2_AccumulationChain.updates query 12=ok (a,b))
    (flush : Port3_FlushInstall.flush b a.weights.deref=ok flushed)
    (size : flushed.val.length=64) (canonical : ∀ q∈flushed.val,Port3_FlushInstall.Canonical q)
    (next : a.next=22#usize) :
    Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed)
      (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value (JGx_Writeback.value a flushed) none=
        ok (.Ok ()) := by
  rw [JGx_FinishAfterPair.source]
  apply (Port3_QueryInstall.success_iff _ ()).mpr
  have dot := JGx_DotGate.source err geometry query a b flushed updates flush size canonical
  exact JGx_FinishDot.source (JGx_Writeback.value a flushed) next dot
#print axioms source
end AspisR1.JGx_Finish
end
