import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee032
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.append_opening_base_row` (callee `prover.append_opening_base_row_loop`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  ∃ next, prover.append_opening_base_row (out := out) (row := row) =
    (prover.append_opening_base_row_loop out row 0#usize >>= next) := by
  unfold prover.append_opening_base_row
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee032
