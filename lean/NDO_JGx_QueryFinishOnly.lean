import NDO_JGx_Finish
import NDO_JGc_TX2_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_QueryFinishOnly
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem source (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (query : Port3_NativeQueryBody.Ops) :
    ∃ a b flushed,
      (Tx2N_Install.inner base true (JGc_TX2_InstalledQuery.raw query)).op6
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator
        JFr_TX2_Powers.value none (JFv_TX2_Geometry.value err geometry)
        JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
      ∀ inactive,
        Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed)
          (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value (JGx_Writeback.value a flushed) none=ok (.Ok ()) := by
  obtain ⟨a,b,flushed,updates,call,weights,next,flush,size,canon⟩ :=
    JGc_TX2_InstalledQuery.source base err geometry query
  exact ⟨a,b,flushed,call,flush,fun inactive=>JGx_Finish.source err geometry
    (JGc_TX2_QueryDictionary.input query) seed inactive a b flushed updates flush size canon next⟩
#print axioms source
end AspisR1.JGx_QueryFinishOnly
end
