import RPz8_RawK_FirstHead
import RPz8_GExq_FirstChildRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_ChildHead
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first {Hash : Type}
    (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (success : S2W_Trace.invoke (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (.op10 D semantic pub proof split hash none) = ok (.Ok saved)) :
    ∃ entry, RawK_CodeHead.head hashv
      (GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv
        (.op10 D semantic pub proof split hash none)) = some entry ∧ entry.1.head? = some 85 := by
  have native := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std)
    D semantic pub proof split hash saved success
  rw [← GExp_FirstPair.installed ops reserved query geo B std] at native
  have raw := (GExq_FirstSource.source (GExp_FirstPair.base ops reserved query geo) B std hashv
    (AspisS6CurrentFirstInstallation.toDigest D) hash law
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split).trans native
  obtain ⟨entry,head,tag⟩ := RawK_FirstHead.first (GExp_FirstPair.base ops reserved query geo)
    B std hashv (AspisS6CurrentFirstInstallation.toDigest D) law
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash saved raw
  refine ⟨entry,?_,tag⟩
  have total := (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv
    (.op10 D semantic pub proof split hash none) ⟨law,rfl⟩).trans success
  exact RawK_CodeHead.left hashv _ _ _ total entry head

#print axioms first
end AspisR1.RawK_ChildHead
end
