import Port7CLEAN_Terminal
import Port6AUTH_Query
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Recovered
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open LiteralAcceptanceTerminal OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortReaderPlumbingC6
open OraclePortFrozenOrderChecks
attribute [local irreducible] LiteralTypedWords.word MatchingSupport.match0
  MatchingSupport.AcceptedPairing QueryResidualBridge.values QueryResidualBridge.basis

/-- Terminal observation transport consuming indexed native authentication,
without a frozen verifier acceptance premise. Duplicate indices are allowed. -/
theorem of_typed (tr : RawCutTranscriptRun.ErasedPrefix)
    (p : Parsed) (q : Fin 22 → Fin 262144)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (query : queries tr = some q)
    (input : OraclePortStoredDecisionDraftC4.input p q tr = some i)
    (checked : D0TypedChecks.verify (typedRows p q tr) i = true)
    (log : List (Bytes × State)) (frames : Fin 3 → Bytes)
    (indexed : ∀ k : Fin 3, ∀ pos, pos<22 →
      OraclePortAllSelectedRecoveryC6.recovered log (frames k) p k.val (index q k.val pos) =
        some (OraclePortPackedChoiceC4.payload p k.val pos)) :
    Nonempty (LiteralAcceptanceTerminal.Checks tr.statement
      (reword (maps log frames p) (typedRows p q tr))) := by
  have fields := (input_fields p q tr i input).1
  have matching := D0TypedChecks.accepted_matching _ i checked
  have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
    simpa [queries,fields.2.1] using query
  have row31 : (typedRows p q tr)[31]? = some (i.m31,
      (TranscriptView.Value.queries (.ok i.queryBytes),i.state31)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.1]
    simp only [Option.map_some,OraclePortCandidateChecksC4.restore_late _ 31
      (by decide) (by decide) (by decide) _ fields.2.2.2.1]
  have row32 : (typedRows p q tr)[32]? = some (i.m32,
      (TranscriptView.Value.ordinary i.rho,i.state32)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.2.1]
    simp only [Option.map_some,OraclePortCandidateChecksC4.restore_late _ 32
      (by decide) (by decide) (by decide) _ fields.2.2.2.2]
  obtain ⟨c⟩ := OraclePortObservationTransportC6.ofTyped tr.statement (typedRows p q tr) i q
    fields.1 row31 row32 fields.2.2.2.1 fields.2.2.2.2 decoded checked
  have dataSame : c.data = i.data := Option.some.inj (c.matchingRead.symm.trans matching)
  have tags := congrArg (fun mc : LiteralTranscript.Message × LiteralTranscript.Challenge => mc.2.1)
    (Option.some.inj (c.entry31.symm.trans row31))
  have bytesSame : c.queryBytes = i.queryBytes := by
    injection tags with same
    injection same
  have querySame : c.queries = q := by
    have h := c.queryDecode
    rw [bytesSame,decoded] at h
    exact (Option.some.inj h).symm
  have selected (k : Fin 3) (j : Fin 22) := OraclePortPackedChoiceC4.packed_agrees p q k.val
    (OraclePortAllSelectedRecoveryC6.recovered log (frames k) p k.val) (indexed k) j.val j.isLt
  have first (j : Fin 22) : packed p q 0 (q j).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 (q j).val := by
    have h := selected (0 : Fin 3) j
    change packed p q 0 (index q 0 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 (index q 0 j.val) at h
    simpa only [index_query,show (0:Nat) ≠ 2 by decide,ite_false] using h
  have second (j : Fin 22) : packed p q 1 (q j).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 (q j).val := by
    have h := selected (1 : Fin 3) j
    change packed p q 1 (index q 1 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 (index q 1 j.val) at h
    simpa only [index_query,show (1:Nat) ≠ 2 by decide,ite_false] using h
  have final (j : Fin 22) : packed p q 2 (parentIndex (n := 65536) (q j)).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 (parentIndex (n := 65536) (q j)).val := by
    have h := selected (2 : Fin 3) j
    change packed p q 2 (index q 2 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 (index q 2 j.val) at h
    simpa only [index_query,ite_true] using h
  have readerWords := OraclePortCandidateWordsC6.reader_words p q tr i.data matching
  have init := OraclePortMapObservationsC6.initial_fibres
    (fun n => packed p q 0 n.val) (fun n => packed p q 1 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 n.val) q first second
  have fin := OraclePortMapObservationsC6.final_selected
    (fun n => packed p q 0 n.val) (fun n => packed p q 1 n.val)
    (fun n => packed p q 2 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 n.val) q final
  obtain ⟨transported⟩ := OraclePortObservationTransportC6.transport tr.statement (typedRows p q tr) c
    (maps log frames p)
    (by rw [dataSame,querySame,readerWords.1]; exact init)
    (by rw [dataSame,querySame,readerWords.2]; exact fin.1)
    (by rw [dataSame,querySame,readerWords.2]; exact fin.2)
  exact OraclePortSelectedConsumerC6.toLiteral_nonempty transported

#print axioms of_typed
end AspisR1.Port7CLEAN_Recovered
end
