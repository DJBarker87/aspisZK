import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_028
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
  Logged (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error)
  := do
  let _ ← observe .saltDerivation 0 (ok ())
  let r ← PV_L1_Logged.lift (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index)
  let r1 ← PV_L1_Logged.lift (core.result.Result.map_err
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ())
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← PV_L1_Logged.lift (alloc.vec.Vec.push salts val)
    Pure.pure (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual

theorem complete_result
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
  erase (produce reserved context hash tag index salts) = prover.derive_private_salt_step reserved context hash tag index salts := by
  unfold produce
  conv_rhs => unfold prover.derive_private_salt_step
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_028
