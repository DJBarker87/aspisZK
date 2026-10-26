import R1Z.ProverRwP6BodyStore
import R1Z.PV_CB_Borrow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_HeapCompatibility
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- filled reads only these two ExternalFuns entries. Backend Vec construction,
resize and Result branching are shared definitions, not dictionary premises. -/
theorem filled_congr (left right : ExternalFuns)
    (reserve : @ExternalFuns.op32 _ left = @ExternalFuns.op32 _ right)
    (mapError : @ExternalFuns.op12 _ left = @ExternalFuns.op12 _ right)
    {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T) :
    @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ left T copy n value =
    @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ right T copy n value := by
  unfold ProverRwSuccessHeapSource.aspis_core.r0.heap.filled
  simp only [alloc.vec.Vec.try_reserve_exact,core.result.Result.map_err,reserve,mapError]

/-- Specialize the CB dictionary to the installed caller: raw op12 is arbitrary. -/
theorem reserve (ops : ExternalFuns) :
    @ExternalFuns.op32 _ (PV_CB_Borrow.selected (ProverRwP6BodyStore.selected ops)) =
      @ExternalFuns.op32 _ (ProverRwSuccessBodyInterpretation.selected ops) := rfl
theorem mapError (ops : ExternalFuns) :
    @ExternalFuns.op12 _ (PV_CB_Borrow.selected (ProverRwP6BodyStore.selected ops)) =
      @ExternalFuns.op12 _ (ProverRwSuccessBodyInterpretation.selected ops) := rfl

theorem dictionary (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _
      (PV_CB_Borrow.selected (ProverRwP6BodyStore.selected ops)) T copy n value =
    @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _
      (ProverRwSuccessBodyInterpretation.selected ops) T copy n value :=
  filled_congr _ _ (reserve ops) (mapError ops) copy n value

#print axioms filled_congr
#print axioms reserve
#print axioms mapError
#print axioms dictionary
end R1Z.PV_Join_HeapCompatibility
