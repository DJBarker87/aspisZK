import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_007
import PV_L1D_Source_020
import PV_L1D_Source_027
import PV_L1D_Source_030
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_031
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  Logged (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let _ ← observe .opening 0 (ok ())
  let (reserved, context) := salts
  let r ← PV_L1D_Source_027.produce variant hash backend sem
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← PV_L1D_Source_030.produce reserved context hash 114#u8
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← PV_L1D_Source_020.produce variant hash val val1
      let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        PV_L1D_Source_007.produce variant val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

theorem complete_result
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  erase (produce public1 variant hash backend sem salts) = prover.prove_from_semantics public1 variant hash backend sem salts := by
  unfold produce
  conv_rhs => unfold prover.prove_from_semantics
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_007.complete_result,PV_L1D_Source_020.complete_result,PV_L1D_Source_027.complete_result,PV_L1D_Source_030.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_007.complete_result,PV_L1D_Source_020.complete_result,PV_L1D_Source_027.complete_result,PV_L1D_Source_030.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_007.complete_result,PV_L1D_Source_020.complete_result,PV_L1D_Source_027.complete_result,PV_L1D_Source_030.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_031
