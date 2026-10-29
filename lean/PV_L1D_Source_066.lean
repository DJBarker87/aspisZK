import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_065
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_066
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Logged (core.result.Result (Array (Array aspis_core.field.QM31 29#usize)
    3#usize) r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let points ← PV_L1D_Logged.lift (r1_wire.statement_points point)
  let a ← PV_L1D_Logged.lift (Array.index_usize points 0#usize)
  let r ← PV_L1D_Source_065.produce columns a
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a1 ← PV_L1D_Logged.lift (Array.index_usize points 1#usize)
    let r1 ← PV_L1D_Source_065.produce columns a1
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a2 ← PV_L1D_Logged.lift (Array.index_usize points 2#usize)
      let r2 ← PV_L1D_Source_065.produce columns a2
      let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        Pure.pure (core.result.Result.Ok (Array.make 3#usize [ val, val1, val2 ]))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
      (core.convert.FromSame r1_wire.Error) residual

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  erase (produce columns point) = host_semantic.point_claims columns point := by
  unfold produce
  conv_rhs => unfold host_semantic.point_claims
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_065.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_065.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_065.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_066
