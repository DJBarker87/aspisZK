import R1FinalSoundnessBinPerQueryR9
import R9PoolConcreteExperiment

/-! The R9 endpoint specialised to the constructed logical saved-ten/Pool
model. This deletes transport for that instance only; equality with frozen
Rust remains a separate source refinement, not an assumed probability. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessBinPerQueryR9Pool
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

abbrev totalBound := BinPerQueryNumeric.totalBound
abbrev Qmax := BinPerQueryNumeric.Qmax

open R9DeployedBinaryExperiment
open R9PoolConcreteExperiment

/-- Verbatim model-instance baseline, retaining transport for signature audit. -/
theorem final_soundness_with_transport
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (tape : Tape) (policy : Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
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
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire_tag : BoundaryEvidence s → RWireCompletion.InitialTag D d P (Q + 1161))
    (h_R9_transport : BoundaryEvidence s → DeployedTransport D d P (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)))
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
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100)) := by
  exact R1FinalSoundnessBinPerQueryR9.final_soundness
    D d P Q (tx1 D P tape) (poolTx2 D d P policy) hqueries s evidence source
    h_R16_instance h_R13 h_R14_backend h_R15_writer h_R3_semantic
    h_Rwire_tag h_R9_transport e p h_M10_ledger h_M10_log_length


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
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
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
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire_tag : BoundaryEvidence s → RWireCompletion.InitialTag D d P (Q + 1161))
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
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100)) := by
  exact R1FinalSoundnessBinPerQueryR9.final_soundness
    D d P Q (tx1 D P tape) (poolTx2 D d P policy) hqueries s evidence source
    h_R16_instance h_R13 h_R14_backend h_R15_writer h_R3_semantic
    h_Rwire_tag (fun _ => deployed_transport D d P tape policy) e p h_M10_ledger h_M10_log_length

#print axioms final_soundness_with_transport
#print axioms final_soundness
end AspisR1.R1FinalSoundnessBinPerQueryR9Pool
end
