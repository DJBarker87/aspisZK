import OraclePortAccLogTransport
import OraclePortShortCircuitHeadline

/-! Conditional draft headline. The sole signature replacement is the strictly
weaker AcceptedRunJoin. No frozen source is claimed to inhabit it; the raw
slot schedule obstruction is independent of this sound transport theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineAccLog
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open OraclePortRuntimeBindingC7 OraclePortShortCircuit OraclePortHeadlineDVsc OraclePortAccLog
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Coins)

theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    Claims D P Q runtime := by
  have hb := OraclePortStoredProbabilityC7.failure_bound D P Q hqueries
  have ht : failureModel runtime ≤ totalBound Q := by
    have hr := OraclePortAccLog.runtime_transport D rust P runtime h_Rust_equals_dV h_stored_runtime
    have hp := add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound
    apply hp.trans_eq
    unfold totalBound OraclePortHeadlineDV.totalBound OraclePortHeadlineLedgerC7.totalBound
      OraclePortHeadline.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_, ?_, R1FinalSoundnessNumeric.extractor_abort_allowance, ht, ?_⟩
  · intro H ha
    have same := projected_sc_accepted_eq D P H ha
    rw [same] at ha ⊢
    exact (RawExtractorCostComposedBin.accepted_attempt_cost
      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
      (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ ha
      (OraclePortStoredProbabilityC7.log_length D P Q hqueries H)).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((ActualCostedExtractorM10.extractor.value run coins).symm.trans hw)
  · intro hlo hhi
    exact ht.trans (OracleDecisionMultiNumeric.safe_range Q hlo hhi)

theorem per_query
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (hlo : 32 ≤ Q) (hhi : Q ≤ Qmax) :
    failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) :=
  (final_soundness D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.2 hlo hhi


#print axioms final_soundness
#print axioms per_query
end AspisR1.OraclePortHeadlineAccLog
end
