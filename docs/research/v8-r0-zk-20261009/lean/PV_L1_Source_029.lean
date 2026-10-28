import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_028
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_029
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) :
  Logged (ControlFlow ((core.result.Result (alloc.vec.Vec (Array Std.U8
    32#usize)) verifier.Error) × Std.Usize) (core.result.Result (alloc.vec.Vec
    (Array Std.U8 32#usize)) verifier.Error))
  := do
  let _ ← observe .saltDerivation 0 (ok ())
  if index < count
  then
    let result1 ← PV_L1_Logged.lift (match result with
      | core.result.Result.Ok salts =>
        do
        let i ← PV_L1_Logged.lift (Aeneas.Std.lift (UScalar.cast .U32 index))
        PV_L1_Source_028.produce reserved context hash tag i salts
      | core.result.Result.Err _ => Pure.pure result)
    let index1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add index 1#usize))
    Pure.pure (cont (result1, index1))
  else Pure.pure (done result)

theorem complete_result
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) :
  erase (produce reserved context hash tag count result index) = prover.derive_private_salts_loop.body reserved context hash tag count result index := by
  unfold produce
  conv_rhs => unfold prover.derive_private_salts_loop.body
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_028.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_028.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_028.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_029
