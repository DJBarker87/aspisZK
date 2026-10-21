import OraclePortShortCircuitTransport
import OraclePortHeadlineDVC7

/-! Conditional OUTER-short-circuit headline. dV_sc below repairs only the
six-slot caller, retaining the existing padding-first/recursive inner model.
It is not the requested exact frozen-order decision; that item is obstructed
by the independent inner schedules documented in SHORTCIRCUIT-DRAFT.
No source premise is discharged or advertised as strictly weaker. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineDVsc
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open OraclePortRuntimeBindingC7 OraclePortShortCircuit
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Coins)

abbrev dV_sc := outerDecision
abbrev totalBound := OraclePortHeadlineDV.totalBound
abbrev Qmax := OraclePortHeadlineDV.Qmax
abbrev failureModel := OraclePortHeadlineDV.failureModel

def projected_sc (D : LiteralByteProtocol.Decoder) (P : Prover) : Experiment :=
  bind (annotated D dV_sc (canon P)) fun v => .done ((v.1.statement,v.1.proof),v.2)

theorem projected_sc_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (projected_sc D P) = view (eval H (annotated D dV_sc (canon P))) := by
  simp only [projected_sc,eval_bind,eval,List.append_nil,view]

theorem projected_sc_accepted_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (eval H (projected_sc D P)).2.2 = true) :
    eval H (projected_sc D P) = eval H (projected D P) := by
  rw [projected_sc_eval] at ha ⊢
  rw [projected_eval,annotated_accepted_eq D (canon P) H ha]

/-- Same claims as the C7 headline, with its accepted extractor experiment
specialized to the outer short-circuit decision. -/
def Claims (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) (runtime : Runtime) : Prop :=
    (∀ H : Bytes → State, (eval H (projected_sc D P)).2.2 = true →
      mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (projected_sc D P)) coins).2.total : ℚ)) ≤
          ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (failureModel runtime ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax → failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100))

/-- No extra premise: the same query cap and stored-runtime binding as C7,
with execution equality retargeted to outerDecision. That retargeting is not
a premise deletion and is not asserted weaker than the C7 source join. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : OuterExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    Claims D P Q runtime := by
  have hb := OraclePortStoredProbabilityC7.failure_bound D P Q hqueries
  have ht : failureModel runtime ≤ totalBound Q := by
    have hr := runtime_transport D rust P runtime h_Rust_equals_dV h_stored_runtime
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
    (h_Rust_equals_dV : OuterExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (hlo : 32 ≤ Q) (hhi : Q ≤ Qmax) :
    failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) :=
  (final_soundness D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.2 hlo hhi

#print axioms projected_sc_eval
#print axioms projected_sc_accepted_eq
#print axioms final_soundness
#print axioms per_query
end AspisR1.OraclePortHeadlineDVsc
end
