import OraclePortShortCircuitAccounting

/-! Acceptance-sensitive transport. Rejected recorded logs need not be a
prefix, since annotation repeats the verifier suffix. No such claim is used. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortShortCircuit
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortRuntimeBindingC7

theorem original_verdict (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (original D outerDecision P)).2.2 = (eval H (original D dV P)).2.2 := by
  rw [original_eval,original_eval]
  exact verifier_verdict D _ H

theorem original_accepted_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (eval H (original D outerDecision P)).2.2 = true) :
    eval H (original D outerDecision P) = eval H (original D dV P) := by
  rw [original_eval] at ha
  rw [original_eval,original_eval,verifier_accepted_eq D _ H ha]

theorem annotated_verdict (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (annotated D outerDecision P)).2.2 = (eval H (annotated D dV P)).2.2 := by
  rw [recorded_eval,recorded_eval]
  exact original_verdict D P H

theorem annotated_accepted_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotated D outerDecision P)).2.2 = true) :
    eval H (annotated D outerDecision P) = eval H (annotated D dV P) := by
  rw [recorded_eval] at ha
  have same := original_accepted_eq D P H ha
  rw [recorded_eval,recorded_eval,same]
  have hv : (eval H (verifier D outerDecision (eval H (original D dV P)).2.1)).2 = true := by
    rw [original_eval] at ha ⊢
    exact ha
  dsimp only
  rw [verifier_accepted_eq D _ H hv]

/-- This is an outer-only source join. It does not identify frozen
batch_tree/verify_in_place order with the unchanged inner dV programs. -/
def OuterExecutionJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ i, rust i = verifier D outerDecision i

theorem annotatedWith_outer (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (join : OuterExecutionJoin D rust) (P : Prover) :
    annotatedWith D rust P = annotated D outerDecision P := by
  have same : rust = verifier D outerDecision := funext join
  rw [same]
  rfl

/-- Same deployed failure comparison as C7, using only equality of accepted
annotated runs. Rejected runs have zero failure mass. -/
theorem runtime_transport (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover)
    (runtime : Runtime) (join : OuterExecutionJoin D rust)
    (binding : StoredCarrierBinding D rust P runtime) :
    deployedFailure runtime ≤
      lazyMean (projected D P) emptyTable
        RawRecordedOracleExtractionMassBin.failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact failure_nonnegative _
  | some run =>
    change RawRecordedOracleExtractionMassBin.failureMass (view run) ≤
      RawRecordedOracleExtractionMassBin.failureMass (eval H (projected D P))
    by_cases accepted : run.2.2 = true
    · have same := binding H run hr accepted
      rw [annotatedWith_outer D rust join] at same
      have ha : (eval H (annotated D outerDecision (canon P))).2.2 = true := by
        rw [← same]; exact accepted
      rw [annotated_accepted_eq D (canon P) H ha] at same
      rw [same,projected_eval]
    · have zero : RawRecordedOracleExtractionMassBin.failureMass (view run) = 0 := by
        unfold RawRecordedOracleExtractionMassBin.failureMass
        simp only [view] at *
        simp [accepted,indicator,
          mean_const]
      rw [zero]
      exact failure_nonnegative _

#print axioms original_verdict
#print axioms original_accepted_eq
#print axioms annotated_verdict
#print axioms annotated_accepted_eq
#print axioms annotatedWith_outer
#print axioms runtime_transport
end AspisR1.OraclePortShortCircuit
end
