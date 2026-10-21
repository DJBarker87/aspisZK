import OraclePortShortCircuitHeadline

/-! Ordered caller substitution retargeted to the outer-short-circuit model.
The remaining inner-order obstruction is not hidden by this interface. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortShortCircuit
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortJoinSplit

structure OuterOrderingJoin {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool) : Prop where
  source_order : ∀ i, rust i = interpret source (tree i)
  model_order : ∀ i, interpret model (tree i) = verifier D outerDecision i

theorem outer_execution_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (_h_S10 : S10Join inventory tree)
    (h_order : OuterOrderingJoin D rust source model tree) : OuterExecutionJoin D rust := by
  intro i
  exact (h_order.source_order i).trans ((interpret_eq h_cones (tree i)).trans
    (h_order.model_order i))

/-- The old eager false-head/reading-tail counterexample disappears at the
outer loop itself, without imposing a hypothesis about the suffix. -/
theorem false_head_stops (rest : List (Program Bytes State Bool)) :
    short (.done false :: rest) = .done false := rfl

theorem rejected_head_log (first : Program Bytes State Bool)
    (rest : List (Program Bytes State Bool)) (H : Bytes → State)
    (rejects : (eval H first).2 = false) :
    eval H (short (first::rest)) = ((eval H first).1,false) := by
  simp only [short,eval_bind,rejects,Bool.false_eq_true,if_false,eval,List.append_nil]

/-- Concrete retargeting of the headline through the ordered caller split.
The constructor parameters are still obligations, not frozen artifacts. -/
theorem final_soundness_of_outer_cones
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime)
    (σ : Signature) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (h_S10 : S10Join inventory tree)
    (h_order : OuterOrderingJoin D rust source model tree)
    (h_stored_runtime : StoredCarrierBinding D rust P runtime) :
    OraclePortHeadlineDVsc.Claims D P Q runtime :=
  OraclePortHeadlineDVsc.final_soundness D P Q hqueries rust runtime
    (outer_execution_of_cones D rust source model tree inventory h_cones h_S10 h_order)
    h_stored_runtime

#print axioms outer_execution_of_cones
#print axioms false_head_stops
#print axioms rejected_head_log
#print axioms final_soundness_of_outer_cones
end AspisR1.OraclePortShortCircuit
end
