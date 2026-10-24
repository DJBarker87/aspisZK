import Port1_CanonicalJoin
import OraclePortFrozen2Headline

/-! The headline with a source-indexed join, retaining the exact existing
StoredCarrierBinding, cost, event, bounds and query accounting. No runtime
binding or concrete raw frozen2 identity is assumed discharged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_CanonicalHeadline
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortFrozen2Consumer
open OraclePortRuntimeBindingC7 RawRecordedOracleExtractionMassBin
open Port1_StoredCarrier
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

theorem lift_queries (P : ByteProver) (Q : Nat)
    (h : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    ∀ H : Bytes → State, (eval H (lift P)).1.length ≤ Q := by
  intro H
  simpa only [lift_eval] using h H

/-- Runtime binding is literally the previous boundary, specialized to the
byte-prover lift; accepted equality now uses only the carried input class. -/
theorem runtime_transport (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : ByteProver) (runtime : Runtime)
    (join : Port1_CanonicalJoin.AcceptedRunJoin D rust)
    (binding : StoredCarrierBinding D rust (lift P) runtime) :
    deployedFailure runtime ≤ lazyMean (projected D (lift P)) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact failure_nonnegative _
  | some run =>
    change failureMass (view run) ≤ failureMass (eval H (projected D (lift P)))
    by_cases accepted : run.2.2 = true
    · have same := binding H run hr accepted
      have ha : (eval H (annotatedWith D rust (canon (lift P)))).2.2 = true := by
        rw [← same]; exact accepted
      rw [Port1_CanonicalJoin.accepted_experiment D rust join P H ha] at same
      rw [same,projected_eval]
    · have zero : failureMass (view run) = 0 := by
        unfold failureMass
        simp only [view] at *
        simp [accepted,indicator,mean_const]
      rw [zero]
      exact failure_nonnegative _

theorem final_soundness (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (join : Port1_CanonicalJoin.AcceptedRunJoin D rust)
    (binding : StoredCarrierBinding D rust (lift P) runtime) :
    OraclePortHeadlineFrozen2.Claims D (lift P) Q runtime := by
  have queries := lift_queries P Q hqueries
  have hb := OraclePortFrozen2Probability.failure_bound D (lift P) Q queries
  have ht : OraclePortHeadlineFrozen2.failureModel runtime ≤ OraclePortHeadlineFrozen2.totalBound Q := by
    have hr := runtime_transport D rust P runtime join binding
    have hp := add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound
    apply hp.trans_eq
    unfold OraclePortHeadlineFrozen2.totalBound OraclePortHeadlineDV.totalBound OraclePortHeadlineLedgerC7.totalBound
      OraclePortHeadline.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_, ?_, R1FinalSoundnessNumeric.extractor_abort_allowance, ht, ?_⟩
  · intro H ha
    change (eval H (projected D (lift P))).2.2 = true at ha
    exact (RawExtractorCostComposedBin.accepted_attempt_cost
      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
      (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ ha
      (OraclePortFrozen2Probability.log_length D (lift P) Q queries H)).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((ActualCostedExtractorM10.extractor.value run coins).symm.trans hw)
  · intro hlo hhi
    exact ht.trans (OracleDecisionMultiNumeric.safe_range Q hlo hhi)

#print axioms lift_queries
#print axioms runtime_transport
#print axioms final_soundness
#print final_soundness
end AspisR1.Port1_CanonicalHeadline
end
