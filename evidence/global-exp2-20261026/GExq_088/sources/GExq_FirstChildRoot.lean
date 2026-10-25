import GExq_FirstRoot
import GExq_ChildCode
import GExq_ContainingRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_FirstChildRoot
open Aeneas Aeneas.Std Result CheckpointBytes5Effect FS2.Duplex

theorem frame {F C Hash : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (success : S2W_Trace.invoke (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (.op10 D semantic pub proof split hash none) = ok (.Ok saved))
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val) :
    ∃ frame, GExq_ContainingRead.Reads hashv
        (GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv
          (.op10 D semantic pub proof split hash none)) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) := by
  have native := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std)
    D semantic pub proof split hash saved success
  rw [← GExp_FirstPair.installed ops reserved query geo B std] at native
  have raw := (GExq_FirstSource.source (GExp_FirstPair.base ops reserved query geo) B std hashv
    (AspisS6CurrentFirstInstallation.toDigest D) hash law
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split).trans native
  obtain ⟨frame,read,target⟩ := GExq_FirstRoot.frame (GExp_FirstPair.base ops reserved query geo)
    B std hashv (AspisS6CurrentFirstInstallation.toDigest D) law
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash saved raw parsed wire
  refine ⟨frame,?_,target⟩
  have total := (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv
    (.op10 D semantic pub proof split hash none) ⟨law,rfl⟩).trans success
  exact GExq_CodeTrace.left_read hashv _ _ _ total frame read

#print axioms frame
end AspisR1.GExq_FirstChildRoot
end
