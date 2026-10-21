import OraclePortActualAcceptanceC6
import OraclePortRowsCanonicalC6

/-! Accepted checks on the actual annotated canonical stored experiment.
Canonicalization preserves erased bytes and prover reads; it supplies the
literal constructor schedule needed by the retained consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortCanonicalAcceptanceC6
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortCompactDraft OraclePortSelectedDraft
open OraclePortStoredAdmissionC4 OraclePortReachedRunC6
attribute [local irreducible] LiteralByteProtocol.protocol LiteralByteSampler.samp

theorem canonical_valid (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run D (canon P) H).2.2 = true) :
    ∀ row, row < 33 → LiteralTranscript.valid row ((input (canon P) H).proof row) := by
  have ha : (run D P H).2.2 = true := by
    change (eval H (original D decision P)).2.2 = true
    rw [← canon_acceptance D decision P H]
    exact accepted
  have decisionAccepted := OraclePortReachedRunC6.accepted D P H ha
  have guard := (OraclePortStoredDecisionDraftC4.accepted _ _ _ H decisionAccepted).1
  have shape := D0ScheduleAdmission.shape_of_schedule D H (input P H).statement (input P H).proof guard.2.1
  intro row bound
  simpa only [OraclePortReachedRunC6.input,canon_eval,canonInput] using R16CanonReduction.valid_of_shape (input P H).proof shape row bound

/-- Canonical restored rows are exactly the compiler's actual rows. This is
a schedule/restoration identity, not equality of old and new word maps. -/
theorem rows_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run D (canon P) H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144) :
    OraclePortReaderPlumbingC6.reword
      (BinCompiledRunWordStability.wordsFromRun D (view (run D (canon P) H)))
      (OraclePortStoredDecisionDraftC4.typedRows p q (reached D (canon P) H)) =
      rows D decision (canon P) H := by
  let w := BinCompiledRunWordStability.wordsFromRun D (view (run D (canon P) H))
  have hpub : (output D decision (canon P) H).statement = (input (canon P) H).statement := by
    unfold output annotated
    rw [recorded_eval,original_eval]
  have hproof : (output D decision (canon P) H).proof =
      RawCutTranscriptRun.proof w (input (canon P) H).proof := by
    unfold output annotated
    rw [recorded_eval]
    rfl
  have validRows : ∀ n (bound : n < (transcript D (canon P) H).rounds.length),
      LiteralTranscript.valid n ((transcript D (canon P) H).rounds[n]'bound).1 := by
    intro n bound
    have length : (transcript D (canon P) H).rounds.length = 33 := LiteralByteRunFacts.transcript_round D H _ _ 33
    have small : n < 33 := by omega
    have at := LiteralByteRunFacts.transcript_index D H (input (canon P) H).statement (input (canon P) H).proof 33 n small
    rw [List.getElem?_eq_getElem bound] at at
    have msg := congrArg Prod.fst (Option.some.inj at)
    rw [msg]
    exact canonical_valid D P H accepted n small
  have restored := OraclePortRowsCanonicalC6.rows p q w (transcript D (canon P) H) validRows
  rw [restored]
  unfold OraclePortStoredAdmissionC4.rows
  rw [hpub,hproof,RawCutTranscriptRun.transcript_eq]
  rfl

/-- R16 construction and the R13/R15/R3/R14 model checks are supplied by
acceptance and collision exclusion, on this exact canonical stored carrier. -/
theorem accepted_checks (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run D (canon P) H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (run D (canon P) H).1) :
    Nonempty (LiteralAcceptanceTerminal.Checks (output D decision (canon P) H).statement
      (rows D decision (canon P) H)) := by
  have hq' : ∀ H : Bytes → State, (eval H (canon P)).1.length ≤ Q := by
    intro H
    simpa only [canon_eval] using hq H
  obtain ⟨p,q,_,_,checks⟩ := OraclePortActualAcceptanceC6.accepted_checks D (canon P) H Q hq' accepted clean
  rw [rows_eq D P H accepted p q] at checks
  have hpub : (output D decision (canon P) H).statement = (input (canon P) H).statement := by
    unfold output annotated
    rw [recorded_eval,original_eval]
  rw [hpub]
  exact checks

#print axioms canonical_valid
#print axioms rows_eq
#print axioms accepted_checks
end AspisR1.OraclePortCanonicalAcceptanceC6
end
