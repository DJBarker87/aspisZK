import RawChecksAdaptiveFailureNoModelBin
import RawRecordedExtractorBranchTraceBin
import RawRecordedLogLengthBin
import R1FinalSoundnessNumericBin

/-! C3 over the genuinely binary recorded extractor and causal decoder.
The source hypothesis names and external premise carriers match C3; binary
clean-word alignment is proved rather than supplied. Cost composition is
added separately with its explicit size-restricted implementation contract. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessBin
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler RawCutTranscriptRun
open RawRecordedOracleExtractionMassBin DecoderInstanceBoundaryBin
open RecordedBinaryExperimentBin LiteralAcceptanceTerminal
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin
abbrev BoundaryStatements := R1FinalSoundness.BoundaryStatements
abbrev BoundaryEvidence := R1FinalSoundness.BoundaryEvidence

theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (deployedFailure : ℚ)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
    /- R4 row31: concrete QueryScan/library/ROM coupling; QUERYSCAN, owner Codex. -/
    (h_R4_row31 : ∀ H, FS2.accepts (eval H (original D d P)) →
      (source H).queryBytes.Nodup ∧ (source H).queryBytes.length = 22 ∧
        ∀ x ∈ (source H).queryBytes, x < 262144)
    /- R13: accepted binary reads give literal matching data; R13-CLOSE,
       batch A on S7, owner Codex. -/
    (h_R13 : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data)
    /- R14 backend: pairing and finalized accumulator; R14-FINISH,
       S4/S5/S8/S9 boundaries, owner Codex. -/
    (h_R14_backend : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    /- R15 writer: authenticated first-match state; TX1-FINISH and read/write
       audits, unconditional frozen-writer preservation still owed, owner Codex. -/
    (h_R15_writer : ∀ H, FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    /- R3/R2: actual semantic endpoint with arithmetic/allocation/circle
       boundaries; HCHECKS field table, owner Codex. -/
    (h_R3_semantic : ∀ H, FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data)
    /- R18: deployed tag/public mapping; SAMPLER-ROWS and DECODER-INSTANCE. -/
    (h_R18 : BoundaryEvidence s → ∀ H,
      (eval H (original D d P)).2.1.1.tag = 2)
    /- R19 with R10: all prefixes, designated-core scope; QV-STAGE1/2 and
       complete log/stop/backend correspondence; owner Codex. -/
    (h_R19 : BoundaryEvidence s → ∀ H,
      firstReads emptyTable (eval H (original D d P)).1 ≤
        Q + (QvStage1.stage1Budget 10 + QvStage2.stage2Budget 12))
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire : BoundaryEvidence s → BinaryCompletion D d P (Q + 1161))
    /- R9/R20: same statement, caller reachability and probability law,
       including a single query-scan abort charge; owner Codex/lead-worker. -/
    (h_R9_transport : BoundaryEvidence s → DeployedTransport D d P deployedFailure)
    /- Adversary experiment restriction, M9 hN: at most 33 recognized starts. -/
    (hN : ∀ H : Bytes → State, DecodedFirstReadUnionBound.decoderFirstReads dec
      emptyTable (eval H (recorded D d P)).1 ≤ 33)
    (e : RawExtractorCostComposedBin.CostedExtractor) (p : Parameters)
    /- Size-restricted M10 adequacy; length is independent of distinct reads. -/
    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement e p Q)
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    (deployedFailure ≤ R1FinalSoundnessNumeric.totalBound Q) ∧
    (Q ≤ R1FinalSoundnessNumeric.maxAdversaryQueries → deployedFailure < 1 / (2 : ℚ)^100) := by
  have hchecks : ∀ H, FS2.accepts (eval H (original D d P)) →
      Checks (compiledPublic D d P H) (compiledRows D d P H) := by
    intro H ha
    obtain ⟨hpub, h31, h32, hv31, hv32⟩ := h_R16_instance evidence H ha
    obtain ⟨hpair, haccum⟩ := h_R14_backend H ha
    exact Classical.choice (hchecks_deployed_partial D d P H
      (source H).decoded (source H).data hpub (h_R13 H ha) hpair
      (source H).m31 (source H).queryBytes (source H).state31
      (source H).m32 (source H).rho (source H).state32
      h31 h32 hv31 hv32 (h_R4_row31 H ha) (h_R15_writer H ha) haccum (h_R3_semantic H ha))
  have hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q + 1161 := by
    simpa only [R1FinalSoundnessNumeric.verifier_reads] using h_R19 evidence
  have hqc := RawCutCompilerLaw.query_bound_preserved D d
    (BinCompiledRunWordStability.wordsFromRun D) P (Q + 1161) hQ
  let inj : AcceptedAdaptiveFiatShamir.LazyInj (LiteralByteProtocol.protocol D) dec
      (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d)
      BinCombinedMerkleCollision.kappa (Q + 1161) :=
    { Coll := binaryCollision (Q + 1161)
      mass := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
        (Q + 1161) (recorded D d P) hqc
      decodes := h_Rwire evidence }
  have h_R12_binary_words : BinaryClean D d P (Q + 1161) :=
    RawChecksAdaptiveFailureNoModelBin.binaryClean_of_checked_acceptance
      D d P (Q + 1161) hQ hchecks (h_Rwire evidence)
  have hb := RawRecordedActualAdaptiveFailureBoundBin.actual_recorded_failure_le_collision_add_start_density_add_abort
    D RawFullPublicSelection.select LiteralTableWordChoiceBin.choose
    (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d)
    BinCombinedMerkleCollision.kappa (Q + 1161) 33 inj
    h_R12_binary_words hN
  have hd : deployedFailure ≤ R1FinalSoundnessNumeric.totalBound Q := by
    calc
      deployedFailure ≤ lazyMean (recorded D d P) emptyTable failureMass +
          QueryScanModelFailure.failureProbability (2^18) := h_R9_transport evidence
      _ ≤ (BinCombinedMerkleCollision.kappa (Q + 1161) +
          (33 : ℚ) * PerAttemptEnvelope.B + 1 / (2 : ℚ)^126) + 1 / (2 : ℚ)^454 :=
        add_le_add hb QueryScanModelFailure.exhaustion_bound
      _ = R1FinalSoundnessNumeric.totalBound Q := by
        rfl
  have hcost : ∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ) := by
    intro H ha
    exact (accepted_attempt_cost e p Q h_M10_ledger _ ha
      (h_M10_log_length evidence H ha)).2
  have hreturned : ∀ run coins w, (e.eval run coins).1 = some w →
      LiteralProtocol.relation run.2.1.1 w := by
    intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((e.value run coins).symm.trans hw)
  exact ⟨hcost, hreturned,
    R1FinalSoundnessNumeric.extractor_abort_allowance, hd,
    fun h => hd.trans_lt ((R1FinalSoundnessNumeric.numeric_iff Q).2 h)⟩

/-- The same uniformly fixed polynomial bounds every size-restricted
member of a Bin implementation family when its actual ledger and coordinate
bounds have been supplied. Neither adequacy premise is inferred from value. -/
theorem uniform_cost (family : Nat → RawExtractorCostComposedBin.CostedExtractor)
    (params : Nat → Parameters) (a k c : Nat)
    (h_M10_ledger : ∀ Q, RawExtractorCostComposedBin.LedgerRefinement
      (family Q) (params Q) Q)
    (h_M10_uniform : ∀ Q, RawExtractorParameterPolynomial.CoordinateBound
      (params Q) (Q + c) a k)
    (Q : Nat) (run : RunView) (ha : run.2.2 = true)
    (hlog : run.1.length ≤ Q + 1161) :
    AspisV8R19.OracleResampling.mean (fun coins : Coins =>
      (((family Q).eval run coins).2.total : ℚ)) ≤
      (Nat.cast ((queryPolynomial a k c).eval Q) : ℚ) :=
  accepted_attempt_polynomial family params a k c h_M10_ledger h_M10_uniform Q run ha hlog

#print axioms final_soundness
#print axioms uniform_cost

end AspisR1.R1FinalSoundnessBin
end
