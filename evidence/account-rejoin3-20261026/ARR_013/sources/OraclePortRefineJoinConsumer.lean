import OraclePortRefineJoinCore

/-! The exact acceptance-only probability consequence. A recorded-run
extractor failure is not such an event: it depends on the recorded log and
on the annotation words, not only on the common Input. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRefineJoin
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
attribute [local instance] Classical.propDecidable

def inputFailure (bad : Input → Prop) (run : View Bytes State (Input × Bool)) : ℚ :=
  indicator (run.2.2 = true ∧ bad run.2.1)

theorem acceptance_event_transport (source model : Verifier)
    (h : AcceptedRefinement source model) (P : Prover) (bad : Input → Prop) :
    lazyMean (originalWith source P) emptyTable (inputFailure bad) ≤
      lazyMean (originalWith model P) emptyTable (inputFailure bad) := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  simp only [originalWith,eval_bind,eval,List.append_nil,inputFailure]
  apply indicator_mono
  rintro ⟨ha,hbad⟩
  exact ⟨(h H (eval H P).2 ha).1,hbad⟩

theorem acceptance_failure_bound (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : ExecutionRefinement D rust) (P : Prover) (bad : Input → Prop) (bound : ℚ)
    (hb : lazyMean (originalWith (verifier D OraclePortShortCircuit.outerDecision) P)
      emptyTable (inputFailure bad) ≤ bound) :
    lazyMean (originalWith rust P) emptyTable (inputFailure bad) ≤ bound :=
  (acceptance_event_transport rust (verifier D OraclePortShortCircuit.outerDecision)
    h P bad).trans hb

#print axioms acceptance_event_transport
#print axioms acceptance_failure_bound
end AspisR1.OraclePortRefineJoin
end
