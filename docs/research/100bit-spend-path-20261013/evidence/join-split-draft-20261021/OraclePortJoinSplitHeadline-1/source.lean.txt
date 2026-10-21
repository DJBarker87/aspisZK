import OraclePortHeadlineDVC7
import OraclePortJoinSplitCore
import OraclePortJoinSplitDecision

/-! Distinct sibling endpoint. This is conditional factorization of C7's
execution premise, not a frozen-source discharge or approval of the port.
StoredCarrierBinding is retained verbatim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortJoinSplitHeadline
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortJoinSplit

/-- Controlled before-signature: the execution premise is redundant only
because the complete split premises are already present. -/
theorem final_soundness_with_execution
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (σ : Signature) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (h_S10 : S10Join inventory tree)
    (h_order : CompositionOrderingJoin D rust source model tree)
    (h_Rust_equals_dV : ExecutionJoin D rust)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    OraclePortHeadlineDV.Claims D P Q runtime :=
  OraclePortHeadlineDV.final_soundness D P Q hqueries rust runtime
    h_Rust_equals_dV h_stored_runtime

/-- Conjunction of total cone joins plus the ordered caller identities feeds
the unmodified draft headline. None of these source joins is constructed here. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (σ : Signature) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (h_S10 : S10Join inventory tree)
    (h_order : CompositionOrderingJoin D rust source model tree)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    OraclePortHeadlineDV.Claims D P Q runtime :=
  OraclePortHeadlineDV.final_soundness D P Q hqueries rust runtime
    (executionJoin_of_cones D rust source model tree inventory h_cones h_S10 h_order)
    h_stored_runtime

theorem per_query
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (σ : Signature) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (h_S10 : S10Join inventory tree)
    (h_order : CompositionOrderingJoin D rust source model tree)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime)
    (hlo : 32 ≤ Q) (hhi : Q ≤ OraclePortHeadlineDV.Qmax) :
    OraclePortHeadlineDV.failureModel runtime ≤ (Q+1:ℚ)*(1/(2:ℚ)^100) :=
  OraclePortHeadlineDV.per_query D P Q hqueries rust runtime
    (executionJoin_of_cones D rust source model tree inventory h_cones h_S10 h_order)
    h_stored_runtime hlo hhi

#print axioms final_soundness_with_execution
#print axioms final_soundness
#print axioms per_query
end AspisR1.OraclePortJoinSplitHeadline
end
