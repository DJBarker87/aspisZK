import R1FinalSoundnessBinPerQueryM10Closed

/-! Headline v2: compose the existing logical Pool headline and closed M10
ledger, retaining every non-M10 evidence field and source law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessHeadlineV2
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
/-- The v1 boundary inventory with only M10_uniform deleted. -/
structure BoundaryStatements where
  P1 : Prop
  P2 : Prop
  P2_prime : Prop
  P3 : Prop
  P4 : Prop
  P5 : Prop
  P6 : Prop
  P7 : Prop
  R10 : Prop
  R22 : Prop
  R4_transport : Prop
  R17 : Prop
  R20 : Prop
  R21 : Prop
  S1 : Prop
  S2 : Prop
  S3 : Prop
  S4 : Prop
  S5 : Prop
  S6 : Prop
  S7 : Prop
  S8 : Prop
  S9 : Prop
  S10 : Prop

/-- The v1 evidence inventory with only h_M10_uniform deleted. -/
structure BoundaryEvidence (s : BoundaryStatements) : Prop where
  h_P1 : s.P1
  h_P2 : s.P2
  h_P2_prime : s.P2_prime
  h_P3 : s.P3
  h_P4 : s.P4
  h_P5 : s.P5
  h_P6 : s.P6
  h_P7 : s.P7
  h_R10 : s.R10
  h_R22 : s.R22
  h_R4_transport : s.R4_transport
  h_R17 : s.R17
  h_R20 : s.R20
  h_R21 : s.R21
  h_S1 : s.S1
  h_S2 : s.S2
  h_S3 : s.S3
  h_S4 : s.S4
  h_S5 : s.S5
  h_S6 : s.S6
  h_S7 : s.S7
  h_S8 : s.S8
  h_S9 : s.S9
  h_S10 : s.S10

/-- Internal compatibility adapter; no claim about the caller's M10 proposition. -/
def legacyStatements (s : BoundaryStatements) : R1FinalSoundness.BoundaryStatements where
  P1 := s.P1
  P2 := s.P2
  P2_prime := s.P2_prime
  P3 := s.P3
  P4 := s.P4
  P5 := s.P5
  P6 := s.P6
  P7 := s.P7
  R10 := s.R10
  R22 := s.R22
  R4_transport := s.R4_transport
  R17 := s.R17
  R20 := s.R20
  R21 := s.R21
  S1 := s.S1
  S2 := s.S2
  S3 := s.S3
  S4 := s.S4
  S5 := s.S5
  S6 := s.S6
  S7 := s.S7
  S8 := s.S8
  S9 := s.S9
  S10 := s.S10
  M10_uniform := True

def legacyEvidence {s : BoundaryStatements} (h : BoundaryEvidence s) :
    R1FinalSoundness.BoundaryEvidence (legacyStatements s) where
  h_P1 := h.h_P1
  h_P2 := h.h_P2
  h_P2_prime := h.h_P2_prime
  h_P3 := h.h_P3
  h_P4 := h.h_P4
  h_P5 := h.h_P5
  h_P6 := h.h_P6
  h_P7 := h.h_P7
  h_R10 := h.h_R10
  h_R22 := h.h_R22
  h_R4_transport := h.h_R4_transport
  h_R17 := h.h_R17
  h_R20 := h.h_R20
  h_R21 := h.h_R21
  h_S1 := h.h_S1
  h_S2 := h.h_S2
  h_S3 := h.h_S3
  h_S4 := h.h_S4
  h_S5 := h.h_S5
  h_S6 := h.h_S6
  h_S7 := h.h_S7
  h_S8 := h.h_S8
  h_S9 := h.h_S9
  h_S10 := h.h_S10
  h_M10_uniform := True.intro

/-- Deleting the field weakens the evidence requirement, without replacements. -/
def ofLegacy (s : R1FinalSoundness.BoundaryStatements)
    (h : R1FinalSoundness.BoundaryEvidence s) :
    BoundaryEvidence {P1 := s.P1, P2 := s.P2, P2_prime := s.P2_prime, P3 := s.P3, P4 := s.P4, P5 := s.P5, P6 := s.P6, P7 := s.P7, R10 := s.R10, R22 := s.R22, R4_transport := s.R4_transport, R17 := s.R17, R20 := s.R20, R21 := s.R21, S1 := s.S1, S2 := s.S2, S3 := s.S3, S4 := s.S4, S5 := s.S5, S6 := s.S6, S7 := s.S7, S8 := s.S8, S9 := s.S9, S10 := s.S10} where
  h_P1 := h.h_P1
  h_P2 := h.h_P2
  h_P2_prime := h.h_P2_prime
  h_P3 := h.h_P3
  h_P4 := h.h_P4
  h_P5 := h.h_P5
  h_P6 := h.h_P6
  h_P7 := h.h_P7
  h_R10 := h.h_R10
  h_R22 := h.h_R22
  h_R4_transport := h.h_R4_transport
  h_R17 := h.h_R17
  h_R20 := h.h_R20
  h_R21 := h.h_R21
  h_S1 := h.h_S1
  h_S2 := h.h_S2
  h_S3 := h.h_S3
  h_S4 := h.h_S4
  h_S5 := h.h_S5
  h_S6 := h.h_S6
  h_S7 := h.h_S7
  h_S8 := h.h_S8
  h_S9 := h.h_S9
  h_S10 := h.h_S10


abbrev totalBound := BinPerQueryNumeric.totalBound
abbrev Qmax := BinPerQueryNumeric.Qmax

open R9DeployedBinaryExperiment R9PoolConcreteExperiment

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
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ ((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100)) := by
  exact R1FinalSoundnessBinPerQueryM10Closed.final_soundness
    D d P Q tape policy hqueries (legacyStatements s) (legacyEvidence evidence) source
    (fun _ => h_R16_instance evidence) h_R13 h_R14_backend h_R15_writer h_R3_semantic
    (fun _ => h_Rwire_tag evidence) (fun _ => h_M10_log_length evidence)

/-- The same accepted recorded experiment has the explicit cubic cost bound.
This composes the closed direct bound and finite-tape mean; no new cost premise. -/
theorem accepted_cost_cubic
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    ∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤
          ((4 * CostedAllocationLedgerM10.scale^3 * (Q+1162)^3 : Nat) : ℚ) := by
  intro H ha
  have pointwise (coins : Coins) :
      ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ) ≤
        ((4 * CostedAllocationLedgerM10.scale^3 * (Q+1162)^3 : Nat) : ℚ) := by
    have hb := ClosedAllocationLedgerM10.direct_bound Q (eval H (recorded D d P)) coins ha
      (h_M10_log_length evidence H ha)
    unfold ActualCostedExtractorM10.extractor
    change ((ActualResourceEvalM10.eval (eval H (recorded D d P)) coins).2.total : ℚ) ≤ _
    exact_mod_cast hb
  exact (FS.mean_mono pointwise).trans (le_of_eq (AspisV8R19.OracleResampling.mean_const _))

#print axioms legacyStatements
#print axioms legacyEvidence
#print axioms ofLegacy
#print axioms final_soundness
#print axioms accepted_cost_cubic
end AspisR1.R1FinalSoundnessHeadlineV2
end
