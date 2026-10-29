import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_030
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) :
  Logged (core.result.Result host_commitment.PrivateSalts verifier.Error)
  := do
  let _ ← observe .saltDerivation 0 (ok ())
  let count ← PV_L1D_Logged.lift (aspis_core.r0.FIBRE_COUNT)
  let (r, salts) ← PV_L1D_Logged.lift (alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (Array Std.U8
      32#usize)) count)
  let r1 ← PV_L1D_Logged.lift (core.result.Result.map_err
      prover.derive_private_salts.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      r ())
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let result ← PV_L1D_Logged.lift (prover.derive_private_salts_loop reserved context hash tag count
        (core.result.Result.Ok salts) 0#usize)
    core.result.Result.map (BuiltinFnOnce (alloc.vec.Vec (Array Std.U8
      32#usize)) host_commitment.PrivateSalts) result
      (host_commitment.PrivateSalts.new)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.PrivateSalts (core.convert.FromSame verifier.Error)
      residual

theorem complete_result
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) :
  erase (produce reserved context hash tag) = prover.derive_private_salts reserved context hash tag := by
  unfold produce
  conv_rhs => unfold prover.derive_private_salts
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
end PV_L1D_Source_030
