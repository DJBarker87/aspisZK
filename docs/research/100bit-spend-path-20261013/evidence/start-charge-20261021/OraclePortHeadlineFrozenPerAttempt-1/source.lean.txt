import StartChargeProbability
import StartChargeNumeric

/-! Probability-level repair of the adopted endpoint. The source and runtime
premises are verbatim those of OraclePortHeadlineFrozen.final_soundness.
The accepted experiment, extractor, collision mass and abort terms are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineFrozenPerAttempt
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortFrozenOrderConsumer
open OraclePortRuntimeBindingC7 OraclePortFrozenOrderJoin
open RawExtractorCostComposedV2 (Coins)

abbrev totalBound := StartChargeNumeric.totalBound
abbrev Qmax := OraclePortHeadlineFrozen.Qmax
abbrev failureModel := OraclePortHeadlineFrozen.failureModel

def Claims (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) (runtime : Runtime) : Prop :=
    (∀ H : Bytes → State, (eval H (OraclePortHeadlineFrozen.projected_frozen D P)).2.2 = true →
      mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval
          (eval H (OraclePortHeadlineFrozen.projected_frozen D P)) coins).2.total : ℚ)) ≤
          ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (failureModel runtime ≤ totalBound Q) ∧
    (Q ≤ Qmax → failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100))

theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    Claims D P Q runtime := by
  have old := OraclePortHeadlineFrozen.final_soundness D P Q hqueries rust runtime
    h_Rust_equals_dV h_stored_runtime
  have hb := StartChargeProbability.failure_bound D P Q hqueries
  have hr := OraclePortFrozenOrderJoin.runtime_transport D rust P runtime
    h_Rust_equals_dV h_stored_runtime
  have ht : failureModel runtime ≤ totalBound Q := by
    apply (add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound).trans_eq
    unfold totalBound StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  exact ⟨old.1,old.2.1,old.2.2.1,ht,
    fun hQ => ht.trans (StartChargeNumeric.safe_range Q hQ)⟩

/-- Explicit repeated/adaptive-attempt bound, without a lower bound on Q. -/
theorem failure_bound
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    failureModel runtime ≤ ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B +
      BinCombinedMerkleCollision.kappa (Q+1161) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 := by
  have ht := (final_soundness D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.1
  exact ht

/-- The same upper query range as the adopted endpoint, with its 32-query
lower bound removed. The explicit repeated-attempt bound remains above. -/
theorem per_query
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (hhi : Q ≤ Qmax) :
    failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) :=
  (final_soundness D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.2 hhi

/-- Clause (A) at the whole-experiment level, including collision, bank-abort
and query-scan exhaustion mass. No work normalization or grinding credit. -/
theorem zero_queries
    (D : LiteralByteProtocol.Decoder) (P : Prover)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ 0)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    failureModel runtime ≤ 1/(2:ℚ)^100 :=
  ((final_soundness D P 0 hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.1).trans
    StartChargeNumeric.zero_queries

#print axioms final_soundness
#print axioms failure_bound
#print axioms per_query
#print axioms zero_queries
end AspisR1.OraclePortHeadlineFrozenPerAttempt
end
