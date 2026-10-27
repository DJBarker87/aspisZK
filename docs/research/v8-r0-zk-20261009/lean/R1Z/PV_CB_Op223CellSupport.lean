import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223CellSupport
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
abbrev Compressor := M → Slice M → Q → Result Q

theorem cell (ops : ExternalFuns) (f : Compressor)
    (columns : Slice (alloc.vec.Vec M)) (column row : Usize) (offset : M) :
    @host_semantic.copy_cell _ {ops with op223 := f} columns column row offset =
    @host_semantic.copy_cell _ ops columns column row offset := rfl
#print axioms cell
end R1Z.PV_CB_Op223CellSupport
