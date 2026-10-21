import OraclePortCandidateWordsC6
import OraclePortFrozenOrderSelectedRecovery
import OraclePortFrozenOrderAccepted

/-! Selected-byte recovery, typed-reader transport and the retained consumer
compose on one containing log. Actual-run commitment-frame placement remains
explicit in the statement; it is not inferred from a free checksum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortFrozenOrderChecks
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open LiteralAcceptanceTerminal OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortReaderPlumbingC6
open OraclePortFrozenOrder
attribute [local irreducible] LiteralTypedWords.word MatchingSupport.match0
  MatchingSupport.AcceptedPairing QueryResidualBridge.values QueryResidualBridge.basis

/-- The natural tree address is exactly the selected typed word index. -/
theorem index_query (q : Fin 22 → Fin 262144) (j : Fin 22) (kind : Nat) :
    index q kind j.val = if kind = 2 then (parentIndex (n := 65536) (q j)).val else (q j).val := by
  have same : (⟨j.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22) = j :=
    Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simp only [index,same,parentIndex]

def maps (log : List (Bytes × State)) (frames : Fin 3 → Bytes) (p : Parsed) :
    CanonicalCutEnrichedTranscript.Words :=
  CanonicalCutEnrichedTranscript.wordsFromMaps
    (fun i => OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 i.val)
    (fun i => OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 i.val)
    (fun i => OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 i.val)

/-- All model checks on cut-recovered rows follow from acceptance, selected
recovery and exact root-frame provenance. No equality to candidate whole rows,
no whole-map equality and no semantic C2-word equality is assumed. -/
theorem accepted_checks (H : Bytes → State) (stored : Bytes)
    (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage)
    (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortStoredParserC4.parseReached stored tr = some p)
    (query : queries tr = some q)
    (accepted : (eval H (dV_frozen stored tr m)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frames : Fin 3 → Bytes) (selectors : Fin 3 → Fin 5)
    (frameRead : ∀ k, Read log (frames k))
    (rootRead : ∀ k, BinRawByteCollisionTargets.pred (selectors k) (frames k) =
      some (committedRoot p k.val)) :
    Nonempty (LiteralAcceptanceTerminal.Checks tr.statement
      (reword (maps log frames p) (typedRows p q tr))) := by
  obtain ⟨_,p',q',i,hp,hq,merkle,input,checked⟩ :=
    OraclePortFrozenOrder.accepted_details stored tr m H accepted
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
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
  have rawParsed := (OraclePortStoredParserC4.parsed stored tr p parsed).1
  have authenticated (k : Fin 3) := OraclePortFrozenOrder.authenticated H stored p rawParsed q
    merkle log Q consistent contains bound clean k.val k.isLt (frames k) (selectors k)
      (frameRead k) (rootRead k)
  have selected (k : Fin 3) (j : Fin 22) := OraclePortPackedChoiceC4.packed_agrees p q k.val
    (OraclePortAllSelectedRecoveryC6.recovered log (frames k) p k.val) (authenticated k) j.val j.isLt
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

#print axioms index_query
#print axioms accepted_checks
end AspisR1.OraclePortFrozenOrderChecks
end
