import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee033
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.audit_masks` (callee `prover.audit_masks_loop0`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) :
  ∃ next, prover.audit_masks (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) =
    (prover.audit_masks_loop0 c1 masks 0#usize 0#usize >>= next) := by
  unfold prover.audit_masks
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee033
