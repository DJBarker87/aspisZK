import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_038
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (values : Slice aspis_core.field.QM31) :
  Logged (Array aspis_core.field.QM31 1024#usize)
  := do
  let _ ← observe .opening 0 (ok ())
  let q ← aspis_core.field.QM31.ZERO
  let out := Array.repeat 1024#usize q
  prover.fixed_k_column_loop values out 0#usize

theorem complete_result
  (values : Slice aspis_core.field.QM31) :
  erase (produce values) = prover.fixed_k_column values := by
  unfold produce prover.fixed_k_column
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_038
