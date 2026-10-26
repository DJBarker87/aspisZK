import F3T_ActualChecks
import F3T_Admission
import OraclePortRowsCanonicalC6

/-! Accepted checks on the actual annotated canonical stored experiment.
Canonicalization preserves erased bytes and prover reads; it supplies the
literal constructor schedule needed by the retained consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.F3T_CanonicalChecks
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment OraclePortCompactDraft OraclePortSelectedDraft
open F3T_Admission F3T_Reached F3T_Canon
attribute [local irreducible] LiteralByteProtocol.protocol LiteralByteSampler.samp FS2.Protocol.transcript

theorem canonical_valid (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run D (canon P) H).2.2 = true) :
    ∀ row, row < 33 → LiteralTranscript.valid row ((input (canon P) H).proof row) := by
  have ha : (run D P H).2.2 = true := by
    change (eval H (original D P)).2.2 = true
    rw [← F3T_Canon.acceptance D P H]
    exact accepted
  have decisionAccepted := F3T_Reached.accepted D P H ha
  have guard := (F3T_Decision.accepted_details (input P H).physical _ _ _ H decisionAccepted).1
  have shape := D0ScheduleAdmission.shape_of_schedule D H (input P H).semantic.value (input P H).proof guard.2.1
  intro row bound
  simpa only [F3T_Reached.input,canon_eval,canonInput] using R16CanonReduction.valid_of_shape (input P H).proof shape row bound

/-- Canonical restored rows are exactly the compiler's actual rows. This is
a schedule/restoration identity, not equality of old and new word maps. -/
theorem rows_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run D (canon P) H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144) :
    OraclePortReaderPlumbingC6.reword
      (BinCompiledRunWordStability.wordsFromRun D (view (run D (canon P) H)))
      (OraclePortStoredDecisionDraftC4.typedRows p q (reached D (canon P) H)) =
      rows D (canon P) H := by
  let w := BinCompiledRunWordStability.wordsFromRun D (view (run D (canon P) H))
  have hpub : (output D (canon P) H).semantic.value = (input (canon P) H).semantic.value := by
    unfold output
    rw [recorded_eval,original_eval]
    rfl
  have hproof : (output D (canon P) H).proof =
      RawCutTranscriptRun.proof w (input (canon P) H).proof := by
    unfold output
    rw [recorded_eval]
    dsimp only [F3T_Experiment.enrich]
    change RawCutTranscriptRun.proof w (eval H (original D (canon P))).2.1.proof = _
    have he : (eval H (original D (canon P))).2.1 = input (canon P) H := by
      rw [original_eval]
    rw [he]
  have validRows : ∀ n (bound : n < (transcript D (canon P) H).rounds.length),
      LiteralTranscript.valid n ((transcript D (canon P) H).rounds[n]'bound).1 := by
    intro n bound
    have length : (transcript D (canon P) H).rounds.length = 33 := LiteralByteRunFacts.transcript_round D H _ _ 33
    have small : n < 33 := by omega
    have entry := LiteralByteRunFacts.transcript_index D H (input (canon P) H).semantic.value (input (canon P) H).proof 33 n small
    rw [List.getElem?_eq_getElem bound] at entry
    have msg := congrArg Prod.fst (Option.some.inj entry)
    rw [msg]
    exact canonical_valid D P H accepted n small
  have restored := OraclePortRowsCanonicalC6.rows p q w (transcript D (canon P) H) validRows
  rw [restored]
  unfold F3T_Admission.rows
  rw [hpub,hproof,RawCutTranscriptRun.transcript_eq]
  rfl

/-- R16 construction and the R13/R15/R3/R14 model checks are supplied by
acceptance and collision exclusion, on this exact canonical stored carrier. -/
theorem accepted_checks (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run D (canon P) H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (run D (canon P) H).1) :
    Nonempty (LiteralAcceptanceTerminal.Checks (output D (canon P) H).semantic.value
      (rows D (canon P) H)) := by
  have hq' : ∀ H : Bytes → State, (eval H (canon P)).1.length ≤ Q := by
    intro H
    simpa only [canon_eval] using hq H
  obtain ⟨p,q,_,_,checks⟩ := F3T_ActualChecks.accepted_checks D (canon P) H Q hq' accepted clean
  rw [rows_eq D P H accepted p q] at checks
  have hpub : (output D (canon P) H).semantic.value = (input (canon P) H).semantic.value := by
    unfold output
    rw [recorded_eval,original_eval]
    rfl
  rw [hpub]
  exact checks

#print axioms canonical_valid
#print axioms rows_eq
#print axioms accepted_checks
end AspisR1.F3T_CanonicalChecks
end
