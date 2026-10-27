import R1Z.PV_CBL_Op35Reference
import R1Z.PV_CBL_Op34Source
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_Op35Source
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { ops with op35 := fun T => PV_CBL_Op35Reference.default_reference (T := T) }

theorem op35_source (ops : ExternalFuns) (T : Type) :
    (selected ops).op35 T = PV_CBL_Op35Reference.default_reference (T := T) := rfl

theorem default_empty (ops : ExternalFuns) (T : Type) :
    (selected ops).op35 T = ok (alloc.vec.Vec.new T) := rfl

theorem op34_preserved (ops : ExternalFuns) :
    @ExternalFuns.op34 _ (selected ops) = @ExternalFuns.op34 _ ops := rfl

#print axioms op35_source
#print axioms default_empty
#print axioms op34_preserved
end R1Z.PV_CBL_Op35Source
