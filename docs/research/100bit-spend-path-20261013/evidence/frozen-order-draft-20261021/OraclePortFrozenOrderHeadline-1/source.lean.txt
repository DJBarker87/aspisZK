import OraclePortFrozenOrderTransport
import OraclePortHeadlineDVC7

/-! Conditional frozen-order draft endpoint. The sole source-verifier
premise is the two-pass AcceptedRunJoin at dV_frozen. StoredCarrierBinding
remains the separate runtime/carrier obligation. No source join is inhabited
by this theorem; no R19 release premise deletion is claimed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineFrozen
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortFrozenOrderConsumer
open OraclePortRuntimeBindingC7 OraclePortFrozenOrderJoin
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Coins)

abbrev dV_frozen := OraclePortFrozenOrder.dV_frozen
abbrev totalBound := OraclePortHeadlineDV.totalBound
abbrev Qmax := OraclePortHeadlineDV.Qmax
abbrev failureModel := OraclePortHeadlineDV.failureModel

def projected_frozen (D : LiteralByteProtocol.Decoder) (P : Prover) : Experiment :=
  bind (annotated D dV_frozen (canon P)) fun v => .done ((v.1.statement,v.1.proof),v.2)

theorem projected_frozen_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (projected_frozen D P) = view (eval H (annotated D dV_frozen (canon P))) := by
  simp only [projected_frozen,eval_bind,eval,List.append_nil,view]

/-- Same claims as the C7 headline, with its accepted extractor experiment
specialized to the frozen-order decision. -/
def Claims (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) (runtime : Runtime) : Prop :=
    (∀ H : Bytes → State, (eval H (projected_frozen D P)).2.2 = true →
      mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (projected_frozen D P)) coins).2.total : ℚ)) ≤
          ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (failureModel runtime ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax → failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100))

theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    Claims D P Q runtime := by
  have hb := OraclePortFrozenOrderProbability.failure_bound D P Q hqueries
  have ht : failureModel runtime ≤ totalBound Q := by
    have hr := runtime_transport D rust P runtime h_Rust_equals_dV h_stored_runtime
    have hp := add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound
    apply hp.trans_eq
    unfold totalBound OraclePortHeadlineDV.totalBound OraclePortHeadlineLedgerC7.totalBound
      OraclePortHeadline.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_, ?_, R1FinalSoundnessNumeric.extractor_abort_allowance, ht, ?_⟩
  · intro H ha
    change (eval H (projected D P)).2.2 = true at ha
    exact (RawExtractorCostComposedBin.accepted_attempt_cost
      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
      (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ ha
      (OraclePortFrozenOrderProbability.log_length D P Q hqueries H)).2
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

#print axioms projected_frozen_eval
#print axioms final_soundness
#print axioms per_query
end AspisR1.OraclePortHeadlineFrozen
end
