import R1Z.PV_CBL_ArraySelection
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_ArraySelectionFrame
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

theorem other_type (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize)
    (v : alloc.vec.Vec T) (ht : T≠PV_CBL_ArrayQM31.Q) :
    @ExternalFuns.op36 _ (PV_CBL_ArraySelection.selected ops) T A N v =
      @ExternalFuns.op36 _ ops T A N v := by
  classical
  change (dite (T=PV_CBL_ArrayQM31.Q ∧ N=1024#usize) _ _) = _
  exact dif_neg (fun h => ht h.1)

theorem reserve (ops : ExternalFuns) :
    @ExternalFuns.op32 _ (PV_CBL_ArraySelection.selected ops) =
      @ExternalFuns.op32 _ ops := rfl

theorem pop (ops : ExternalFuns) :
    @ExternalFuns.op33 _ (PV_CBL_ArraySelection.selected ops) =
      @ExternalFuns.op33 _ ops := rfl
#print axioms other_type
#print axioms reserve
#print axioms pop
end R1Z.PV_CBL_ArraySelectionFrame
