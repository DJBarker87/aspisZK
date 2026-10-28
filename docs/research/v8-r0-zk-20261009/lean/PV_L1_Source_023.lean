import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_023
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) :
  Logged (alloc.vec.Vec aspis_core.field.wide_exact.WideExact)
  := do
  let _ ← observe .opening 0 (ok ())
  let gp ← PV_L1_Logged.lift (weights.powers 29#usize gamma)
  let q :=
    alloc.vec.Vec.with_capacity aspis_core.field.wide_exact.WideExact
      1024#usize
  prover.opening_batch_loop coefficients gp q 0#usize

theorem complete_result
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) :
  erase (produce coefficients gamma) = prover.opening_batch coefficients gamma := by
  unfold produce prover.opening_batch
  simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_023
