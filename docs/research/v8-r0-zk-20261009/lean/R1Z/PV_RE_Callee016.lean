import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee016
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.add_d_tail` (callee `host_semantic.d_tail_side`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) :
  ∃ next, host_semantic.add_d_tail (mask_sum := mask_sum) (dc := dc) =
    (host_semantic.d_tail_side dc 0#usize >>= next) := by
  unfold host_semantic.add_d_tail
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee016
