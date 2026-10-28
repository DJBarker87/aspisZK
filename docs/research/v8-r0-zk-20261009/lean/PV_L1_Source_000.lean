import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_000
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8)
  (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .publication 0 (ok ())
  prover.append_opening_secure_row_loop out row 26#usize

theorem complete_result
  (out : alloc.vec.Vec Std.U8)
  (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  erase (produce out row) = prover.append_opening_secure_row out row := by
  unfold produce prover.append_opening_secure_row
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_000
