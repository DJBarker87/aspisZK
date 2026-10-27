import JGx_QueryFinishOnly
import JGx_Batch
import JGx_RealStatement
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_LocalNonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

/-- Unconditional SAME-byte local computation witness. No actual reader,
SDK prefix, native wrapper or deployed security non-vacuity is asserted. -/
theorem source {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Op5T_Install.stageBatch Port4B_Install.leaves (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      JFx_NativeBytes.proof JFo_Prepared.value JGe_View.folded 1#usize hash=ok (.Ok ()) ∧
    AspisS6CurrentCodecInstallation.encode JGx_RealStatement.value=ok (.Ok JGx_PublicArray.value) ∧
    ∃ a b flushed,
      (Tx2N_Install.inner base true (JGc_TX2_InstalledQuery.raw query)).op6
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator JFr_TX2_Powers.value none
        (JFv_TX2_Geometry.value err geometry) JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
      ∀ inactive,Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed)
        (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value (JGx_Writeback.value a flushed) none=ok (.Ok ()) :=
  ⟨JGx_Batch.source D hash,JGx_RealStatement.encode,JGx_QueryFinishOnly.source base seed err geometry query⟩
#print axioms source
end AspisR1.JGx_LocalNonvacuity
end
