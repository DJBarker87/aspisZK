import OraclePortHeadlineLedgerC7
import ClosedAllocationLedgerM10

/-! Logical stored-aware dV headline with the pinned v3 closed M10 ledger.
This read-only reuse changes no instrumentation module. Frozen Rust equality
and stored-carrier runtime binding remain explicit hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadlineDV
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredConsumerC7 OraclePortRuntimeBindingC7
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Coins)

abbrev totalBound := OraclePortHeadlineLedgerC7.totalBound
abbrev Qmax := OraclePortHeadlineLedgerC7.Qmax
abbrev failureModel := OraclePortHeadlineLedgerC7.failureModel
abbrev Claims (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) (runtime : Runtime) :=
  OraclePortHeadlineLedgerC7.Claims D P Q runtime ActualCostedExtractorM10.extractor
    (CostedAllocationLedgerM10.params (Q+1161))

/-- Before-signature for the controlled deletion-only audit. -/
theorem final_soundness_of_clean
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (h_model : CleanAcceptedModel D (projected D P) (bad Q)) :
    Claims D P Q runtime :=
  OraclePortHeadlineLedgerC7.final_soundness_of_clean D P Q hqueries rust runtime
    h_Rust_equals_dV h_stored_runtime ActualCostedExtractorM10.extractor
    (CostedAllocationLedgerM10.params (Q+1161)) (ClosedAllocationLedgerM10.ledger (Q+1161)) h_model

/-- Completed draft at dO := dV, retaining source/runtime joins. The prover
chooses stored bytes adaptively; no model checks or M10 premise remain. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    Claims D P Q runtime :=
  final_soundness_of_clean D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime
    (OraclePortStoredConsumerC7.clean D P Q hqueries)

/-- Explicit per-query conclusion, including the single scan allowance. -/
theorem per_query
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (hlo : 32 ≤ Q) (hhi : Q ≤ Qmax) :
    failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) :=
  (final_soundness D P Q hqueries rust runtime h_Rust_equals_dV h_stored_runtime).2.2.2.2 hlo hhi

/-- The retained closed ledger stays cubic on the larger issued-log domain. -/
theorem accepted_cost_cubic
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (H : Bytes → State) (ha : (eval H (projected D P)).2.2 = true) :
    mean (fun coins : Coins =>
      ((ActualCostedExtractorM10.extractor.eval (eval H (projected D P)) coins).2.total : ℚ)) ≤
      ((4*CostedAllocationLedgerM10.scale^3*(Q+2323)^3 : Nat) : ℚ) := by
  have hp := OraclePortStoredProbabilityC7.log_length D P Q hqueries H
  have hi : ∀ coins : Coins,
      ((ActualCostedExtractorM10.extractor.eval (eval H (projected D P)) coins).2.total : ℚ) ≤
        ((4*CostedAllocationLedgerM10.scale^3*(Q+2323)^3 : Nat) : ℚ) := by
    intro coins
    apply Nat.cast_le.mpr
    unfold ActualCostedExtractorM10.extractor
    change (ActualResourceEvalM10.eval (eval H (projected D P)) coins).2.total ≤ _
    rw [show Q+2323 = Q+1161+1162 by omega]
    exact ClosedAllocationLedgerM10.direct_bound (Q+1161)
      (eval H (projected D P)) coins ha (by omega)
  exact (mean_mono hi).trans_eq (mean_const _)

#print axioms final_soundness_of_clean
#print axioms final_soundness
#print axioms per_query
#print axioms accepted_cost_cubic
end AspisR1.OraclePortHeadlineDV
end
