import OraclePortStoredConsumerC7

/-! Controlled same-carrier premise deletion audit. The normalization from
v3's pure pair carrier to fixed stored-input fibres is a separate change.
These adapters do not claim source equality with frozen Rust. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPremiseDeletionC7
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortStoredReductionC7 OraclePortStoredConsumerC7
open RecordedBinaryExperimentBin (SourceInputs)
open RawRecordedOracleExtractionMassBin

theorem model_stage0
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_R16_instance : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      OraclePortAdmission.InstanceFields D (dV s) (pairProver s P) H (source H))
    (h_R13 : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      LiteralMatchingData.read (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) = some (source H).data)
    (h_R14_backend : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      LiteralPairingChecks.checks (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    (h_R15_writer : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    (h_R3_semantic : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) (source H).data)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage1
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_R13 : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      LiteralMatchingData.read (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) = some (source H).data)
    (h_R14_backend : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      LiteralPairingChecks.checks (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    (h_R15_writer : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    (h_R3_semantic : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) (source H).data)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage2
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_R14_backend : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      LiteralPairingChecks.checks (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    (h_R15_writer : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    (h_R3_semantic : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) (source H).data)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage3
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_R15_writer : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    (h_R3_semantic : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) (source H).data)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage4
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_R3_semantic : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H) (source H).data)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage5
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
    (h_Rwire_tag : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_stage6
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

theorem model_without_source
    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
 :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

#print axioms model_stage0
#print axioms model_stage1
#print axioms model_stage2
#print axioms model_stage3
#print axioms model_stage4
#print axioms model_stage5
#print axioms model_stage6
#print axioms model_without_source
end AspisR1.OraclePortPremiseDeletionC7
end
