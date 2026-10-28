import NDO_JGc_TX2_LoopPrefix
import NDO_JFz_TX2_AccumulationFlush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryLoop
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) :
    ∃ a b flushed,
      JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) 12=ok (a,b) ∧
      Port3_QueryStage.query (JFr_TX2_DotsBinding.ops seed)
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator
        JFr_TX2_Powers.value none (JFv_TX2_Geometry.value err geometrySeed)
        JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
      Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q := by
  obtain ⟨a,b,flushed,run,weights,next,flush,size,canon⟩ :=
    JFz_TX2_AccumulationFlush.source err geometrySeed (JGc_TX2_QueryDictionary.input seed)
  refine ⟨a,b,flushed,run,?_,weights,next,flush,size,canon⟩
  apply (Port3_QueryInstall.success_iff _ _).mpr
  rw [JGc_TX2_QueryDictionary.release]
  exact (JGc_TX2_LoopPrefix.source err geometrySeed seed 12 (by omega) a b run).trans
    (JGc_TX2_LoopStep.done _ _ _ _ _ _ _ _ (by rw [next]))
#print axioms source
#print source
end AspisR1.JGc_TX2_QueryLoop
end
