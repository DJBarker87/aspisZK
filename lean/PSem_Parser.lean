import PSem_SemanticRows
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PSem_Parser
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames

/-- Exact remaining interface after semantic-row discharge. Header and scan
are the already derived accepted-run facts; Aligned is still an obligation.
This conditional parser theorem earns no whole-premise removal credit. -/
theorem when_aligned {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (header : OraclePortHeader.accepts (bytesOf proof.val)=true)
    (scan : OraclePortCompactDraft.scan (bytesOf proof.val)) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      ∀ tr : RawCutTranscriptRun.ErasedPrefix,
        Aligned ⟨bytesOf proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩ tr →
        OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=
          some ⟨bytesOf proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩ := by
  obtain ⟨expanded,pre,parsed,rows⟩ := PSem_SemanticRows.on_run
    ops reserved query geo B std D hash pub publicBytes proof split saved run
  exact ⟨expanded,pre,parsed,fun tr aligned =>
    OraclePortStoredParserC4.parse_of_parts _ _ tr header scan rows aligned⟩

#print axioms when_aligned
end AspisR1.PSem_Parser
end
