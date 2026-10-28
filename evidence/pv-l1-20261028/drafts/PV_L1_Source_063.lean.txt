import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_058
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_063
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize) :
  Logged (core.result.Result Unit r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let r ← PV_L1_Logged.lift (host_semantic.check_base_columns c1)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r1 ← PV_L1_Logged.lift (host_semantic.check_secure_column d)
    let cf1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      PV_L1_Source_058.produce g
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame r1_wire.Error) residual

theorem complete_result
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize) :
  erase (produce c1 d g) = host_semantic.check_semantic_columns c1 d g := by
  unfold produce
  conv_rhs => unfold host_semantic.check_semantic_columns
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_058.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_058.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_058.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_063
