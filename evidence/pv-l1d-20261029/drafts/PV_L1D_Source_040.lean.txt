import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_040
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
  Logged (core.result.Result Bool r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let r ← PV_L1D_Logged.lift (host_semantic.lean_copy_row_values compiled.trace lambda)
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← PV_L1D_Logged.lift (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
    let r2 ← PV_L1D_Logged.lift (core.result.Result.map_err
        host_semantic.no_pole.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
        r1 ())
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s := alloc.vec.Vec.deref val
      let b ← PV_L1D_Logged.lift (ct_pole.all_slots_clear s val1 chi)
      Pure.pure (core.result.Result.Ok b)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Bool (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Bool (core.convert.FromSame r1_wire.Error) residual

theorem complete_result
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
  erase (produce compiled lambda chi) = host_semantic.no_pole compiled lambda chi := by
  unfold produce
  conv_rhs => unfold host_semantic.no_pole
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_040
