import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee027
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_wire.parse_record` (callee `r1_wire.row_shape`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (row : Std.U8) (record1 : Slice Std.U8) :
  ∃ next, host_wire.parse_record (row := row) (record1 := record1) =
    (r1_wire.row_shape row >>= next) := by
  unfold host_wire.parse_record
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee027
