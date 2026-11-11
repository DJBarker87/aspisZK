import AspisOneTxRun
import AspisRec40CleanStatement
import OraclePortStoredReductionC7

/-! The Aspis one-transaction verifier: item M9 of ONE-TRANSACTION-GAME.md,
`CheckedAcceptance40` in exactly the shape the rows agent's clean event takes
(`AspisRec40.CleanStatement.CheckedAcceptance40`, copy of R1's
`OraclePortConsumer.CheckedAcceptance`), discharged for the Aspis decision.

Kind of result: MODEL THEOREMS in R1's stored-decision and binary commitment
model. Copies, for the 40-row experiment at `dV_aspis`, of R1's
* `OraclePortFrozen2CanonicalChecks.{canonical_valid, rows_eq, accepted_checks}`
  (with `OraclePortRowsCanonicalC6.rows` restated so that rows 33..39 need only
  the canonical message shape: R1's `LiteralTranscript.valid` admits payload
  rows only below 33);
* `OraclePortFrozen2C6.{original_clean, checked_acceptance}`;
* `OraclePortStoredExperimentC4.{verifier_enrich, recorded_eval}`,
  `OraclePortStoredProjectionC4.{original_view, recorded_view}` and
  `OraclePortStoredReductionC7.{original_fixed, annotated_fixed}` for the
  40-row experiment;
* `OraclePortFrozen2Consumer.fibre_checks`.
The exceptional event is R1's binary collision at `Q + 1111`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisOneTx.Checked
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.OraclePortStoredExperimentC4 AspisR1.OraclePortStoredAdmissionC4
open AspisR1.OraclePortStoredDecisionDraftC4 AspisR1.OraclePortReaderPlumbingC6
open AspisR1.OraclePortCompactDraft
open AspisOneTx AspisOneTx.Run
open AspisAcceptance (AspisChecks)
open CanonicalCutEnrichedTranscript (Words enrichMessage enrichRounds)
attribute [local irreducible] LiteralByteProtocol.protocol LiteralByteSampler.samp FS2.Protocol.transcript

abbrev output40 (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (H : Bytes → State) :=
  (eval H (AspisRec40.HitMass.annotated D d P)).2.1
abbrev rows40 (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (H : Bytes → State) :=
  ((AspisRows40.Protocol.protocol D).transcript H
    (output40 D d P H).statement (output40 D d P H).proof 40).rounds

/-! ### The 40-row experiment: enrichment, recorded run, views -/

theorem verifier_enrich40 (D : LiteralByteProtocol.Decoder) (d : Decision) (w : Words) (i : Input) :
    AspisRec40.HitMass.verifier D d (enrich w i) = AspisRec40.HitMass.verifier D d i :=
  AspisRec40.Decision.verifier_eq D (d i.stored) w i.statement i.proof

theorem recorded_eval40 (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (AspisRec40.HitMass.recorded D d build P) =
      let v := eval H (AspisRec40.HitMass.original D d P)
      (v.1 ++ (eval H (AspisRec40.HitMass.verifier D d v.2.1)).1,
        (enrich (build (view v)) v.2.1,v.2.2)) := by
  rw [AspisRec40.HitMass.recorded,AspisRec40.HitMass.original_eval,AspisRec40.HitMass.compiled_eval]
  dsimp only
  rw [verifier_enrich40]
  have same : (eval H (AspisRec40.HitMass.verifier D d (eval H (AspisRec40.HitMass.original D d P)).2.1)).2 =
      (eval H (AspisRec40.HitMass.original D d P)).2.2 := by
    rw [AspisRec40.HitMass.original_eval]
  rw [same]

theorem original_view40 (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (H : Bytes → State) :
    view (eval H (AspisRec40.HitMass.original D d P)) =
      eval H (AspisRec40.Decision.original D (d (eval H P).2.stored)
        (OraclePortStoredProjectionC4.project P)) := by
  rw [AspisRec40.HitMass.original_eval,AspisRec40.Decision.original,
    RawCutProverCompiler.experiment_eval,OraclePortStoredProjectionC4.project_eval]
  rfl

theorem recorded_view40 (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    view (eval H (AspisRec40.HitMass.recorded D d build P)) =
      eval H (AspisRec40.Decision.annotated D (d (eval H P).2.stored) build
        (OraclePortStoredProjectionC4.project P)) := by
  rw [recorded_eval40,AspisRec40.Decision.annotated,AspisRec40.Decision.compiled_experiment_eval]
  have same := original_view40 D d P H
  change view (eval H (AspisRec40.HitMass.original D d P)) =
    eval H (RawCutProverCompiler.experiment (OraclePortStoredProjectionC4.project P)
      (AspisRec40.Decision.verifier D (d (eval H P).2.stored))) at same
  rw [← same]
  have stored : (eval H (AspisRec40.HitMass.original D d P)).2.1.stored = (eval H P).2.stored := by
    rw [AspisRec40.HitMass.original_eval]
  simp only [view,enrich,AspisRec40.HitMass.verifier]
  rw [stored]

theorem original_fixed40 (D : LiteralByteProtocol.Decoder) (d : Decision) (s : Bytes) (P : Prover)
    (H : Bytes → State) :
    view (eval H (AspisRec40.HitMass.original D d (canon (OraclePortStoredReductionC7.fixStored s P)))) =
      eval H (AspisRec40.Decision.original D (d s) (OraclePortStoredReductionC7.pairProver s P)) := by
  rw [original_view40,canon_eval,OraclePortStoredReductionC7.fixStored_eval]
  rfl

theorem annotated_fixed40 (D : LiteralByteProtocol.Decoder) (d : Decision) (s : Bytes) (P : Prover)
    (H : Bytes → State) :
    view (eval H (AspisRec40.HitMass.annotated D d (canon (OraclePortStoredReductionC7.fixStored s P)))) =
      eval H (AspisRec40.Decision.recorded D (d s) (OraclePortStoredReductionC7.pairProver s P)) := by
  rw [AspisRec40.HitMass.annotated,recorded_view40,canon_eval,OraclePortStoredReductionC7.fixStored_eval]
  rfl

/-! ### Canonical rows (copy of `OraclePortFrozen2CanonicalChecks`) -/

theorem message_idem (i : Nat) (m : LiteralTranscript.Message) :
    R16CanonReduction.message i (R16CanonReduction.message i m) = R16CanonReduction.message i m := by
  by_cases h2 : i = 2 <;> by_cases h30 : i = 30 <;>
    cases m <;> simp [R16CanonReduction.message, h2, h30]

theorem canonical_valid40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run40 D (canon P) H).2.2 = true) :
    ∀ row, row < 33 → LiteralTranscript.valid row ((Run.input (canon P) H).proof row) := by
  obtain ⟨guard,_⟩ := accepted_detailsS _ _ _ H (accepted40 D (canon P) H accepted)
  rw [reached_take33] at guard
  have shape := D0ScheduleAdmission.shape_of_schedule D H (Run.input (canon P) H).statement
    (Run.input (canon P) H).proof guard.2.1
  intro row bound
  have v := R16CanonReduction.valid_of_shape _ shape row bound
  have idem : R16CanonReduction.proof (Run.input (canon P) H).proof = (Run.input (canon P) H).proof := by
    simp only [Run.input,canon_eval,canonInput]
    funext i
    exact message_idem i _
  rw [idem] at v
  exact v

theorem restore_canon_late (w : Words) (n : Nat) (h2 : n ≠ 2) (h30 : n ≠ 30)
    (m : LiteralTranscript.Message) :
    restore w n (LiteralTranscript.erase (R16CanonReduction.message n m)) =
      enrichMessage w (R16CanonReduction.message n m) := by
  cases m <;> simp [R16CanonReduction.message, h2, h30, restore, LiteralTranscript.erase,
    CanonicalCutEnrichedTranscript.enrichMessage]

/-- `OraclePortRowsCanonicalC6.rows` with its validity premise replaced by the
restoration identity it is used for. -/
theorem rows_gen (p : Parsed) (q : Fin 22 → Fin 262144) (w : Words) (P : LiteralTranscript.Prefix)
    (ok : ∀ n (bound : n < P.rounds.length),
      restore w n (LiteralTranscript.erase (P.rounds[n]'bound).1) = enrichMessage w (P.rounds[n]'bound).1) :
    reword w (typedRows p q (LiteralTranscript.erasePrefix P)) = enrichRounds w P.rounds := by
  apply List.ext_getElem
  · simp only [reword,typedRows,LiteralTranscript.erasePrefix,enrichRounds,List.length_map,List.length_mapIdx]
  · intro n hn hm
    simp only [reword,typedRows,LiteralTranscript.erasePrefix,enrichRounds,List.getElem_map,List.getElem_mapIdx]
    apply Prod.ext
    · rw [OraclePortRowsCanonicalC6.enrich_restore]
      exact ok n (by simpa only [reword,typedRows,LiteralTranscript.erasePrefix,
        List.length_map,List.length_mapIdx] using hn)
    · rfl

/-- The restoration identity on every row of a 40-round transcript of a
canonical-shaped proof, stated over abstract public input and proof. -/
theorem ok_gen (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (w : Words)
    (valid : ∀ row, row < 33 → LiteralTranscript.valid row (pf row))
    (late : ∀ n, 33 ≤ n → ∃ m, pf n = R16CanonReduction.message n m) :
    ∀ n (bound : n < ((LiteralByteProtocol.protocol D).transcript H pub pf 40).rounds.length),
      restore w n (LiteralTranscript.erase
        (((LiteralByteProtocol.protocol D).transcript H pub pf 40).rounds[n]'bound).1) =
      enrichMessage w (((LiteralByteProtocol.protocol D).transcript H pub pf 40).rounds[n]'bound).1 := by
  intro n bound
  have length : ((LiteralByteProtocol.protocol D).transcript H pub pf 40).rounds.length = 40 :=
    LiteralByteRunFacts.transcript_round D H pub pf 40
  have small : n < 40 := by omega
  have entry := LiteralByteRunFacts.transcript_index D H pub pf 40 n small
  rw [List.getElem?_eq_getElem bound] at entry
  have msg := congrArg Prod.fst (Option.some.inj entry)
  rw [msg]
  by_cases low : n < 33
  · exact OraclePortRowsCanonicalC6.restore_valid w n _ (valid n low)
  · obtain ⟨m, hm⟩ := late n (by omega)
    rw [hm]
    exact restore_canon_late w n (by omega) (by omega) m

theorem rows_eq40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (run40 D (canon P) H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144) :
    reword (BinCompiledRunWordStability.wordsFromRun D (view (run40 D (canon P) H)))
      (typedRows p q (reached40 D (canon P) H)) = rows40 D dV_aspis (canon P) H := by
  let w := BinCompiledRunWordStability.wordsFromRun D (view (run40 D (canon P) H))
  have hrun : (eval H (AspisRec40.HitMass.original D dV_aspis (canon P))).2.1 = Run.input (canon P) H := by
    rw [AspisRec40.HitMass.original_eval]
  have hout : output40 D dV_aspis (canon P) H = enrich w (Run.input (canon P) H) := by
    unfold output40
    rw [AspisRec40.HitMass.annotated,recorded_eval40]
    dsimp only
    rw [hrun]
  have late : ∀ n, 33 ≤ n → ∃ m, (Run.input (canon P) H).proof n = R16CanonReduction.message n m :=
    fun n _ => ⟨(Run.input P H).proof n, by simp only [Run.input,canon_eval,canonInput]; rfl⟩
  have restored := rows_gen p q w _
    (ok_gen D H (Run.input (canon P) H).statement (Run.input (canon P) H).proof w
      (canonical_valid40 D P H accepted) late)
  have hr : reached40 D (canon P) H = LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H
        (Run.input (canon P) H).statement (Run.input (canon P) H).proof 40) := by
    unfold reached40
    rw [AspisRows40.Protocol.transcript_eq]
  change reword w (typedRows p q (reached40 D (canon P) H)) = _
  rw [hr,restored]
  unfold rows40
  rw [hout]
  dsimp only [OraclePortStoredExperimentC4.enrich]
  rw [AspisRows40.Protocol.transcript_eq,RawCutTranscriptRun.transcript_eq]
  rfl

theorem output_statement40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (output40 D dV_aspis (canon P) H).statement = (reached40 D (canon P) H).statement := by
  have lhs : (output40 D dV_aspis (canon P) H).statement = (eval H (canon P)).2.statement := by
    unfold output40
    rw [AspisRec40.HitMass.annotated,recorded_eval40,AspisRec40.HitMass.original_eval]
    rfl
  have rhs : (reached40 D (canon P) H).statement = (eval H (canon P)).2.statement := by
    unfold reached40 LiteralTranscript.erasePrefix
    rw [AspisRows40.Literal.transcript_statement]
  rw [lhs,rhs]

/-- Copy of `OraclePortFrozen2CanonicalChecks.accepted_checks`. -/
theorem accepted_checks_canon40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run40 D (canon P) H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1111)) emptyTable (run40 D (canon P) H).1) :
    Nonempty (AspisChecks decodePairS (output40 D dV_aspis (canon P) H).statement
      (rows40 D dV_aspis (canon P) H)) := by
  have hq' : ∀ H : Bytes → State, (eval H (canon P)).1.length ≤ Q := by
    intro H
    simpa only [canon_eval] using hq H
  obtain ⟨p,q,_,_,checks⟩ := accepted_checks40 D (canon P) H Q hq' accepted clean
  rw [rows_eq40 D P H accepted p q] at checks
  rw [output_statement40]
  exact checks

/-! ### Checked acceptance (copy of `OraclePortFrozen2C6`) -/

/-- R1's `OraclePortStoredChecksC4.CheckedAcceptance` for the 40-row experiment. -/
def CheckedAcceptanceC4_40 (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q (view (eval H (AspisRec40.HitMass.annotated D d P))) →
    (eval H (AspisRec40.HitMass.original D d P)).2.2 = true →
    Nonempty (AspisChecks decodePairS (output40 D d P H).statement (rows40 D d P H))

theorem original_clean40 (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) (Q : Nat)
    (clean : ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (view (eval H (AspisRec40.HitMass.annotated D d P)))) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (eval H (AspisRec40.HitMass.original D d P)).1 := by
  intro bad
  apply clean
  change hitsBad _ emptyTable (eval H (AspisRec40.HitMass.recorded D d
    (BinCompiledRunWordStability.wordsFromRun D) P)).1
  rw [recorded_eval40]
  exact TraceAppend.hitsBad_of_prefix _ _ _ _ bad

theorem checked_acceptance40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    CheckedAcceptanceC4_40 D dV_aspis (canon P) (Q+1111) := by
  intro H clean accepted
  exact accepted_checks_canon40 D P H Q hq accepted
    (original_clean40 D dV_aspis (canon P) H (Q+1111) clean)

/-! ### M9: the clean event's hypothesis (copy of `OraclePortFrozen2Consumer.fibre_checks`) -/

theorem fibre_checks40 (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    AspisRec40.CleanStatement.CheckedAcceptance40 D (dV_aspis s)
      (OraclePortStoredReductionC7.pairProver s P) (Q+1111) := by
  intro H hc ha
  have checks := checked_acceptance40 D (OraclePortStoredReductionC7.fixStored s P) Q
    (fun H => by rw [OraclePortStoredReductionC7.fixStored_eval]; exact hq H) H
  have orig := original_fixed40 D dV_aspis s P H
  have ann := annotated_fixed40 D dV_aspis s P H
  have hc' : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111)
      (view (eval H (AspisRec40.HitMass.annotated D dV_aspis
        (canon (OraclePortStoredReductionC7.fixStored s P))))) := by
    rw [ann]; exact hc
  have ha' : (eval H (AspisRec40.HitMass.original D dV_aspis
      (canon (OraclePortStoredReductionC7.fixStored s P)))).2.2 = true :=
    (congrArg (fun v : RawCutProverCompiler.RunView => v.2.2) orig).trans ha
  obtain ⟨ch⟩ := checks hc' ha'
  change AspisChecks decodePairS
    (view (eval H (AspisRec40.HitMass.annotated D dV_aspis
      (canon (OraclePortStoredReductionC7.fixStored s P))))).2.1.1
    ((AspisRows40.Protocol.protocol D).transcript H
      (view (eval H (AspisRec40.HitMass.annotated D dV_aspis
        (canon (OraclePortStoredReductionC7.fixStored s P))))).2.1.1
      (view (eval H (AspisRec40.HitMass.annotated D dV_aspis
        (canon (OraclePortStoredReductionC7.fixStored s P))))).2.1.2 40).rounds at ch
  rw [ann] at ch
  exact ⟨ch⟩

#print axioms verifier_enrich40
#print axioms recorded_eval40
#print axioms original_view40
#print axioms recorded_view40
#print axioms original_fixed40
#print axioms annotated_fixed40
#print axioms canonical_valid40
#print axioms rows_gen
#print axioms ok_gen
#print axioms rows_eq40
#print axioms output_statement40
#print axioms accepted_checks_canon40
#print axioms original_clean40
#print axioms checked_acceptance40
#print axioms fibre_checks40
end AspisOneTx.Checked
end
