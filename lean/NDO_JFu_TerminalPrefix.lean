import NDO_JFu_TerminalSelected
import NDO_JFu_Transition
import NDO_JFm_Begin
import NDO_JFm_PartialAlpha
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TerminalPrefix
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

def alpha := FIq_Carriers.mapArray FIq_Carriers.toQ JFm_PartialAlpha.a10
def challenges := FIq_Carriers.toChallenges JFm_Begin.challenges

def tail (selected : Array field.QM31 84#usize) :
    Result (core.result.Result field.QM31 state_only_prefix.r0.Error) := do
  let r ← terminal_parts JFu_PublicSemantic.value selected alpha
    challenges.lambda challenges.chi challenges.theta challenges.zc challenges.mu
  let r1 ← FIq_Native.core.result.Result.map
    r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31 r ()
  FIq_Native.core.result.Result.map_err
    r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error r1 ()

/-- Exact source prefix on the retained Claims/public/alpha/challenges. The unresolved tail is explicit. -/
theorem source : ∃ selected,
    array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
    validate_transition JFu_PublicSemantic.value=ok (.Ok ()) ∧
    r0.Public.terminal_qm31 (FIq_Carriers.toPublic JFs_PublicSerialization.value)
      JFu_TerminalCallback.claims alpha challenges=tail selected := by
  obtain ⟨selected,gather⟩ := JFu_TerminalSelected.source
  refine ⟨selected,gather,JFu_Transition.source,?_⟩
  rw [JFu_PublicSemantic.public_eq]
  unfold r0.Public.terminal_qm31 tail
  rw [gather,bind_tc_ok,JFu_PublicSemantic.source,bind_tc_ok]

#print axioms source
end AspisR1.JFu_TerminalPrefix
end
