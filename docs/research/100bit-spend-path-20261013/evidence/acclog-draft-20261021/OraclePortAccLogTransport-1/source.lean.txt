import OraclePortAccLogCore
import OraclePortRefineJoinExtractionTransport

/-! Complete accepted observations preserve cuts and recovered extractor
inputs without any monotonicity or permutation argument. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAccLog
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open OraclePortRuntimeBindingC7 RawRecordedOracleExtractionMassBin
attribute [local instance] Classical.propDecidable

theorem accepted_original_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : AcceptedRunJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (originalWith rust P)).2.2 = true) :
    eval H (originalWith rust P) = eval H (original D OraclePortShortCircuit.outerDecision P) := by
  rw [originalWith_eval] at ha ⊢
  rw [original_eval,h.verifier H (eval H P).2 ha]

/-- The words fed into enrichment agree on an accepted first pass. -/
theorem accepted_built_words_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : AcceptedRunJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (originalWith rust P)).2.2 = true) :
    build D (view (eval H (originalWith rust P))) =
      build D (view (eval H (original D OraclePortShortCircuit.outerDecision P))) := by
  rw [accepted_original_eq D rust h P H ha]

theorem accepted_recovered_inputs (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : AcceptedRunJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotatedWith D rust P)).2.2 = true) :
    OraclePortRefineJoin.RecoveredInputAgreement
      (view (eval H (annotatedWith D rust P)))
      (view (eval H (annotated D OraclePortShortCircuit.outerDecision P))) := by
  rw [h.annotated P H ha]
  exact ⟨rfl,rfl,rfl⟩

theorem accepted_extractor_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : AcceptedRunJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotatedWith D rust P)).2.2 = true)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract (view (eval H (annotatedWith D rust P))) coins =
      RawRecordedPublicSpendExtractorBin.extract
        (view (eval H (annotated D OraclePortShortCircuit.outerDecision P))) coins :=
  OraclePortRefineJoin.extractor_eq_of_recovered_inputs _ _
    (accepted_recovered_inputs D rust h P H ha) coins

/-- Runtime binding is retained verbatim. Rejected runtime runs have zero
failure mass and impose no equality obligation. -/
theorem runtime_transport (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover)
    (runtime : Runtime) (join : AcceptedRunJoin D rust)
    (binding : StoredCarrierBinding D rust P runtime) :
    deployedFailure runtime ≤ lazyMean (projected D P) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact failure_nonnegative _
  | some run =>
    change failureMass (view run) ≤ failureMass (eval H (projected D P))
    by_cases accepted : run.2.2 = true
    · have same := binding H run hr accepted
      have ha : (eval H (annotatedWith D rust (canon P))).2.2 = true := by
        rw [← same]; exact accepted
      rw [join.annotated (canon P) H ha] at same
      have hs : (eval H (annotated D OraclePortShortCircuit.outerDecision (canon P))).2.2 = true := by
        rw [← same]; exact accepted
      rw [OraclePortShortCircuit.annotated_accepted_eq D (canon P) H hs] at same
      rw [same,projected_eval]
    · have zero : failureMass (view run) = 0 := by
        unfold failureMass
        simp only [view] at *
        simp [accepted,indicator,mean_const]
      rw [zero]
      exact failure_nonnegative _

#print axioms accepted_original_eq
#print axioms accepted_built_words_eq
#print axioms accepted_recovered_inputs
#print axioms accepted_extractor_eq
#print axioms runtime_transport
end AspisR1.OraclePortAccLog
end
