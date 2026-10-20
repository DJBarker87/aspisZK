import R1FinalSoundnessBinPerQueryR19
import RWireCompletion
import R19BudgetOriginalReads

/-! R19 endpoint with binary causal completion derived symbolically from the
existing checked readers and a strictly narrower initial-public tag law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NoCollPremiseWeakening
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

theorem h_R16_instance_of_unconditional
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (s : BoundaryStatements)
    (source : (Bytes → State) → SourceInputs)
    (h : BoundaryEvidence s → ∀ H,
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H)) :
    BoundaryEvidence s → ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) →
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H) := by
  intro evidence H _ ha
  exact h evidence H ha

#print axioms h_R16_instance_of_unconditional

theorem h_R13_of_unconditional
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (source : (Bytes → State) → SourceInputs)
    (h : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data) :
    ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data := by
  intro H _ ha
  exact h H ha

#print axioms h_R13_of_unconditional

theorem h_R14_backend_of_unconditional
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (source : (Bytes → State) → SourceInputs)
    (h : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho)) :
    ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho) := by
  intro H _ ha
  exact h H ha

#print axioms h_R14_backend_of_unconditional

theorem h_R15_writer_of_unconditional
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (source : (Bytes → State) → SourceInputs)
    (h : ∀ H, FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j)) :
    ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j) := by
  intro H _ ha
  exact h H ha

#print axioms h_R15_writer_of_unconditional

theorem h_R3_semantic_of_unconditional
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (source : (Bytes → State) → SourceInputs)
    (h : ∀ H, FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data) :
    ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data := by
  intro H _ ha
  exact h H ha

#print axioms h_R3_semantic_of_unconditional

/-- The restriction drops precisely the obligations on colliding accepted runs. -/
theorem restriction_decomposition {ι : Type} (accept coll fact : ι → Prop) :
    (∀ i, accept i → fact i) ↔
      (∀ i, ¬ coll i → accept i → fact i) ∧
      (∀ i, coll i → accept i → fact i) := by
  classical
  constructor
  · intro h
    exact ⟨fun i _ ha => h i ha, fun i _ ha => h i ha⟩
  · rintro ⟨hn, hc⟩ i ha
    by_cases h : coll i
    · exact hc i h ha
    · exact hn i h ha

/-- The implication cannot be reversed for unrestricted predicates. -/
theorem restriction_is_strict :
    (∀ i : Unit, ¬ True → True → False) ∧
      ¬ (∀ i : Unit, True → False) := by
  exact ⟨fun _ hn _ => hn trivial, fun h => h () trivial⟩

#print axioms restriction_decomposition
#print axioms restriction_is_strict
end AspisR1.NoCollPremiseWeakening
end
