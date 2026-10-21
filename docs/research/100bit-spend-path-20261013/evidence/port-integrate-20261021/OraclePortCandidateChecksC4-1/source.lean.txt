import OraclePortStoredDecisionDraftC4

/-! Acceptance gives HCHECKS on the byte-derived candidate rows. The compiler
uses commitment-cut words; equating its selected reader components with
these rows is a separate, explicitly unproved transport step. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCandidateChecksC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)

theorem restore_late (w : CanonicalCutEnrichedTranscript.Words) (row : Nat)
    (h0 : row ≠ 0) (h2 : row ≠ 2) (h30 : row ≠ 30)
    (m : LiteralTranscript.Message) (valid : LiteralTranscript.valid row m) :
    restore w row (LiteralTranscript.erase m) = m := by
  cases m <;> simp_all [LiteralTranscript.valid,LiteralTranscript.erase,restore]

theorem candidate_checks (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (fields : D0InstanceAdmission.Fields tr i)
    (query : queries tr = some q)
    (checked : D0TypedChecks.verify (typedRows p q tr) i = true) :
    Nonempty (LiteralAcceptanceTerminal.Checks tr.statement (typedRows p q tr)) := by
  have row31 : (typedRows p q tr)[31]? = some (i.m31,
      (TranscriptView.Value.queries (.ok i.queryBytes),i.state31)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.1]
    simp only [Option.map_some,restore_late _ 31 (by decide) (by decide) (by decide) _ fields.2.2.2.1]
  have row32 : (typedRows p q tr)[32]? = some (i.m32,
      (TranscriptView.Value.ordinary i.rho,i.state32)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.2.1]
    simp only [Option.map_some,restore_late _ 32 (by decide) (by decide) (by decide) _ fields.2.2.2.2]
  have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
    simpa [queries,fields.2.1] using query
  obtain ⟨pairing,accumulator⟩ := D0TypedChecks.accepted_backend _ i checked
  exact HchecksReaderComposition.hchecks_partial _ _ i.decoded i.data fields.1
    (D0TypedChecks.accepted_matching _ i checked) pairing
    i.m31 i.queryBytes i.state31 i.m32 i.rho i.state32 row31 row32 fields.2.2.2.1 fields.2.2.2.2
    (QueryScanRow31SourcePlacement.decode_shape _ q decoded)
    (D0TypedChecks.accepted_writer _ i checked) accumulator
    (D0TypedChecks.accepted_semantic _ i checked)

theorem accepted_checks (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State) (ha : (eval H (decision stored tr m)).2 = true) :
    ∃ p q, OraclePortStoredParserC4.parseReached stored tr = some p ∧
      queries tr = some q ∧
      Nonempty (LiteralAcceptanceTerminal.Checks tr.statement (typedRows p q tr)) := by
  obtain ⟨_,p,q,i,parsed,query,_,_,input,checked⟩ := accepted stored tr m H ha
  exact ⟨p,q,parsed,query,candidate_checks p q tr i (input_fields p q tr i input).1 query checked⟩

#print axioms restore_late
#print axioms candidate_checks
#print axioms accepted_checks
end AspisR1.OraclePortCandidateChecksC4
end
