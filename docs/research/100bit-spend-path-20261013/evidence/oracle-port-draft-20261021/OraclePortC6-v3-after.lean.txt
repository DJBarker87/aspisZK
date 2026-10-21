import R1FinalSoundnessHeadlineV2
import R19BudgetOriginalReads

/-! Headline v3: issued queries, including repeated verifier reads, bound the
recorded log. Recording and pure word enrichment add no queries. The compiler
runs one internal verifier and the outer experiment runs a second verifier.
The inherited sampler/program inductions count both passes in full. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessHeadlineV3
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler RawCutTranscriptRun
open RawRecordedOracleExtractionMassBin DecoderInstanceBoundaryBin
open RecordedBinaryExperimentBin LiteralAcceptanceTerminal
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin
open R1FinalSoundnessHeadlineV2
open R9DeployedBinaryExperiment R9PoolConcreteExperiment

/-- Exact chronological log; every repeated read remains in the list. -/
theorem recorded_log_eq
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (eval H (recorded D d P)).1 =
      ((eval H P).1 ++
        (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1) ++
        (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1 := by
  change (eval H (experiment
    (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d))).1 = _
  rw [compiled_experiment_eval]
  simp only [RawCutProverCompiler.experiment_eval]

/-- The prover executes once; each verifier pass costs at most 561 queries.
No acceptance or boundary evidence is needed. -/
theorem recorded_log_length
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    (eval H (recorded D d P)).1.length ≤ Q + 1122 := by
  rw [recorded_log_eq, List.length_append, List.length_append]
  have hp := hqueries H
  have hv := R19BudgetOriginalReads.verifier_queries D d H
    (eval H P).2.1 (eval H P).2.2
  omega

/-- Supply the former M10 size premise with the unchanged 1161 envelope. -/
theorem recorded_log_length_envelope
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    (eval H (recorded D d P)).1.length ≤ Q + 1161 := by
  have h := recorded_log_length D d P Q hqueries H
  omega

theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (tape : Tape) (policy : Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) →
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
    /- R13: accepted binary reads give literal matching data; R13-CLOSE,
       batch A on S7, owner Codex. -/
    (h_R13 : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data)
    /- R14 backend: pairing and finalized accumulator; R14-FINISH,
       S4/S5/S8/S9 boundaries, owner Codex. -/
    (h_R14_backend : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    /- R15 writer: authenticated first-match state; TX1-FINISH and read/write
       audits, unconditional frozen-writer preservation still owed, owner Codex. -/
    (h_R15_writer : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    /- R3/R2: actual semantic endpoint with arithmetic/allocation/circle
       boundaries; HCHECKS field table, owner Codex. -/
    (h_R3_semantic : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data)
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire_tag : BoundaryEvidence s → InitialTagDecision.CheckedRejects D d P (Q + 1161))
    :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ ((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100)) := by
  exact R1FinalSoundnessHeadlineV2.final_soundness
    D d P Q tape policy hqueries s evidence source
    h_R16_instance h_R13 h_R14_backend h_R15_writer h_R3_semantic h_Rwire_tag
    (fun _ H _ => recorded_log_length_envelope D d P Q hqueries H)

/-- The v2 cubic bound with the size premise discharged. -/
theorem accepted_cost_cubic
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s) :
    ∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤
          ((4 * CostedAllocationLedgerM10.scale^3 * (Q+1162)^3 : Nat) : ℚ) := by
  exact R1FinalSoundnessHeadlineV2.accepted_cost_cubic D d P Q s evidence
    (fun _ H _ => recorded_log_length_envelope D d P Q hqueries H)

#print axioms recorded_log_eq
#print axioms recorded_log_length
#print axioms recorded_log_length_envelope
#print axioms final_soundness
#print axioms accepted_cost_cubic
end AspisR1.R1FinalSoundnessHeadlineV3
end
