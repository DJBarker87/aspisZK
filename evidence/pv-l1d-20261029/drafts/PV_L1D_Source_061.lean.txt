import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_060
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_061
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (lane : Std.Usize)
  :
  Logged (ControlFlow Std.Usize (Option (core.result.Result Unit
    r1_wire.Error)))
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  if lane < 26#usize
  then
    let v ← PV_L1D_Logged.lift (Array.index_usize c1 lane)
    let s := alloc.vec.Vec.deref v
    let r ← PV_L1D_Source_060.produce s
    let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let lane1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add lane 1#usize))
      Pure.pure (cont lane1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame r1_wire.Error) residual)
      Pure.pure (done (some r1))
  else Pure.pure (done none)

theorem complete_result
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (lane : Std.Usize) :
  erase (produce c1 lane) = host_semantic.check_base_columns_loop.body c1 lane := by
  unfold produce
  conv_rhs => unfold host_semantic.check_base_columns_loop.body
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_060.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_060.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_060.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_061
