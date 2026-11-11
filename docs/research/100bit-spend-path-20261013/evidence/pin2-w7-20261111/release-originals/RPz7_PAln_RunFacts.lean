import RPz7_PAln_SourceRun
import RPz7_PSem_Root
import RPz7_PSem_SemanticRows
import RPz7_PSem_SemanticTrace
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_RunFacts
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft
def Facts {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) : Prop :=
    ∃ (expanded : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H)
      (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (t0 t25 : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (cs : List (AspisR1PublicPreparation.SourceFull25.Call (retainedDigest D) pre)),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983)=
        some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok t0) ∧
      pre.c1_root.val=PAln_SourceRun.storedRoot proof ∧
      view.semantic=expanded ∧
      PAln_OpeningStages.Double
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries
            (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))
        (retainedDigest D) (retainedSem sem) (retainedView view) hash retained rs ∧
      currentPrepared retained=run.p ∧ AspisR1ClaimPreparedBridge.mapArray currentE rs=run.scratch ∧
      AspisR1PublicPreparation.SourceFull25.Trace (retainedDigest D) pre t0 t25 cs ∧
      cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => bytesOf c.record.framed.val)=
        (pre.records.val.map (fun s => bytesOf s.val)).take 25 ∧
      ∃ record25 record26 z0 t26 z1 t27,
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t25 record25=ok (.Ok z0,t26) ∧
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t26 record26=ok (.Ok z1,t27) ∧
        (retainedSem sem).transcript=t27

theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) : Facts ops reserved query geo B std D hash pub publicBytes proof split saved run :=
  PAln_SourceRun.on_run ops reserved query geo B std D hash pub publicBytes proof split saved run

#print axioms on_run
end AspisR1.PAln_RunFacts
end
