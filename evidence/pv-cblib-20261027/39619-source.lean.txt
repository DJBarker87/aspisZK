import R1Z.PV_CBL_Op34Source
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_SelectionFrame
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

/-- Composition preserves each other assigned callback in full, including
its failure/divergence result and all polymorphic arguments. -/
theorem op25_preserved (ops : ExternalFuns) :
    @ExternalFuns.op25 _ (PV_CBL_Op34Source.selected ops) =
      @ExternalFuns.op25 _ ops := rfl

theorem op26_preserved (ops : ExternalFuns) :
    @ExternalFuns.op26 _ (PV_CBL_Op34Source.selected ops) =
      @ExternalFuns.op26 _ ops := rfl

theorem op28_preserved (ops : ExternalFuns) :
    @ExternalFuns.op28 _ (PV_CBL_Op34Source.selected ops) =
      @ExternalFuns.op28 _ ops := rfl

theorem op29_preserved (ops : ExternalFuns) :
    @ExternalFuns.op29 _ (PV_CBL_Op34Source.selected ops) =
      @ExternalFuns.op29 _ ops := rfl

#print axioms op25_preserved
#print axioms op26_preserved
#print axioms op28_preserved
#print axioms op29_preserved
end R1Z.PV_CBL_SelectionFrame
