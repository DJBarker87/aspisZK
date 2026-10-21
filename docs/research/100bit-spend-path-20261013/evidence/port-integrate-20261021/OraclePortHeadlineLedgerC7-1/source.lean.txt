import OraclePortRuntimeBindingC7
import OraclePortStoredProbabilityModelC7

/-! Completed logical dV draft endpoint. Execution equality with frozen Rust
and the stored-carrier runtime binding are explicit, unproved joins.
R16/R13/R15/R3/R14 model checks and decoder completion are theorems. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineLedgerC7
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open OraclePortRuntimeBindingC7 RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin

abbrev totalBound := OraclePortHeadline.totalBound
abbrev Qmax := OracleDecisionMultiNumeric.safeMax

/-- Single query-scan allowance, retained separately from adaptive failure. -/
abbrev failureModel (runtime : Runtime) : ℚ :=
  deployedFailure runtime + QueryScanModelFailure.failureProbability (2^18)

def Claims (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (runtime : Runtime) (e : CostedExtractor) (p : Parameters) : Prop :=
    (∀ H : Bytes → State, (eval H (projected D P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (projected D P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (failureModel runtime ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax → failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100))

/-- Controlled before-signature for the deletion-only audit. All other
arguments and the conclusion are identical to final_soundness. -/
theorem final_soundness_of_clean
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q+1161))
    (h_model : CleanAcceptedModel D (projected D P) (bad Q)) :
    Claims D P Q runtime e p := by
  have hb := OraclePortStoredProbabilityModelC7.failure_bound_of_clean D P Q hqueries h_model
  have ht : failureModel runtime ≤ totalBound Q := by
    have hr := OraclePortRuntimeBindingC7.transport D rust P runtime h_Rust_equals_dV h_stored_runtime
    have hp := add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound
    apply hp.trans_eq
    unfold totalBound OraclePortHeadline.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_, ?_, R1FinalSoundnessNumeric.extractor_abort_allowance, ht, ?_⟩
  · intro H ha
    exact (accepted_attempt_cost e p (Q+1161) h_M10_ledger _ ha
      (OraclePortStoredProbabilityC7.log_length D P Q hqueries H)).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((e.value run coins).symm.trans hw)
  · intro hlo hhi
    exact ht.trans (OracleDecisionMultiNumeric.safe_range Q hlo hhi)

/-- Completed draft model headline at dO := dV. No ReaderBinding, separate
matching/writer/semantic/backend assumptions, source witness, completion or
free decision remains. M10 and the frozen source/runtime joins remain explicit. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q+1161)) :
    Claims D P Q runtime e p :=
  final_soundness_of_clean D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime
    e p h_M10_ledger (OraclePortStoredConsumerC7.clean D P Q hqueries)

#print axioms final_soundness_of_clean
#print axioms final_soundness
end AspisR1.OraclePortHeadlineLedgerC7
end
