import Mathlib.Tactic.CasesM
import R1Z.PV_RunJoin_PairElimination
import R1Z.ProverRwRetryModel
import R1Z.ProverRwBodyStore
import R1Z.PV_RunJoin_ResultTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_StoreContinuationResidual
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitSemanticTransport26
variable [ExternalTypes] [ExternalFuns]

/-- Exact remaining external dictionary law: map_err must respect the
pointwise error callback across closure carrier types. This is a hypothesis,
not an installed native callback or an axiom. -/
def MapErrParametric : Prop :=
  ∀ {S T E F : Type} (left : core.ops.function.FnOnce S E F)
    (right : core.ops.function.FnOnce T E F) (s : S) (t : T)
    {A : Type} (value : core.result.Result A E),
    (∀ e, left.call_once s e = right.call_once t e) →
      core.result.Result.map_err left value s = core.result.Result.map_err right value t

/-- The first actual emitted error closure is insensitive to the store carrier
under the explicitly named dictionary law. Full continuation transport remains
open; this theorem does not replace that obligation. -/
theorem mask_error_closure_transport (parametric : MapErrParametric)
    {S T A : Type}
    (left : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (right : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (value : core.result.Result A aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
    core.result.Result.map_err
      (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError left)
      value () =
    core.result.Result.map_err
      (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError right)
      value () := by
  exact parametric _ _ () () value (fun _ => rfl)

#print axioms mask_error_closure_transport
end R1Z.PV_RunJoin_StoreContinuationResidual
