import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee014
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_compact.compact_semantic_row` (callee `r1_wire.row_shape`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) :
  ∃ next, host_compact.compact_semantic_row (logical := logical) (out := out) (row := row) (at1 := at1) =
    (r1_wire.row_shape row >>= next) := by
  unfold host_compact.compact_semantic_row
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee014
