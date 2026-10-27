import PAln_DataRead
import PSem_TypedPrefix
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_WhenAligned
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (header : OraclePortHeader.accepts (bytesOf proof.val)=true)
    (scan : scan (bytesOf proof.val)) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983)=
        some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      ∀ (tr : RawCutTranscriptRun.ErasedPrefix) (q : Fin 22 → Fin 262144),
        let parsed : Parsed := ⟨bytesOf proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩
        Aligned parsed tr →
        (∀ i,i<31 → ∃ value,LiteralChallengeRead.ordinaryAt (typedRows parsed q tr) i=some value) →
        ∃ data,LiteralMatchingData.read (typedRows parsed q tr)=some data := by
  obtain ⟨expanded,pre,parsed,rows⟩ := PSem_SemanticRows.on_run
    ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨values,full,encoded,typed⟩ := PSem_TypedPrefix.typed_prefix expanded pre parsed
  have same : PSem_TypedPrefix.completedRecords pre=
      (pre.records.val.map (fun s => bytesOf s.val)).take 25 := by
    simp only [PSem_TypedPrefix.completedRecords,List.map_take]
    rfl
  rw [same] at typed
  refine ⟨expanded,pre,parsed,rows,?_⟩
  intro tr q
  dsimp only
  intro aligned ordinary
  exact PAln_DataRead.exists_read _ q tr aligned rows
    ((OraclePortHeader.accepts_iff _).mp header).1 scan ⟨_,typed⟩ ordinary

#print axioms on_run
end AspisR1.PAln_WhenAligned
end
