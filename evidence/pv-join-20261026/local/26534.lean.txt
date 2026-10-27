import R1Z.PV_Join_Codecs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CodecDictionary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Replace exactly these three fields, retaining every other entry. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BodyStore.selected ops with
    op71 := (PV_CB_Codecs.selected ops).op71
    op72 := (PV_CB_Codecs.selected ops).op72
    op80 := (PV_CB_Phi.selected ops).op80}
/-- The named source laws discharge all three projection equalities. -/
theorem dictionary (ops : ExternalFuns) :
    selected ops = ProverRwP6BodyStore.selected ops := by
  have parse : (PV_CB_Codecs.selected ops).op71 = (ProverRwP6BodyStore.selected ops).op71 := by
    funext bytes
    exact (PV_CB_Op71Source.op71_source ops bytes).trans (PV_Join_Codecs.op71_source ops bytes).symm
  have write : (PV_CB_Codecs.selected ops).op72 = (ProverRwP6BodyStore.selected ops).op72 := by
    funext x bytes
    exact (PV_CB_Op72Source.op72_source ops x bytes).trans (PV_Join_Codecs.op72_source ops x bytes).symm
  have phi : @ExternalFuns.op80 _ (PV_CB_Phi.selected ops) =
      @ExternalFuns.op80 _ (ProverRwP6BodyStore.selected ops) := by
    funext E inst x y h
    exact (PV_CB_Op80Source.op80_source ops inst x y h).trans (PV_Join_Codecs.op80_source ops inst x y h).symm
  unfold selected
  rw [parse, write, phi]
  rfl
#print axioms dictionary
end R1Z.PV_Join_CodecDictionary
