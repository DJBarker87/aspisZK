import R1Z.PV_CB_Borrow
import R1Z.ProverRwSuccessHeapInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Heap
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Reservation callback is retained in the emitted source, including errors. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Borrow.selected ops with op81 :=
    @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ (PV_CB_Borrow.selected ops)}
theorem op81_source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    (selected ops).op81 copy n value =
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ (PV_CB_Borrow.selected ops) T copy n value := rfl
theorem op32_preserved (ops : ExternalFuns) {T : Type} (A : Type)
    (v : alloc.vec.Vec T) (n : Usize) :
    (selected ops).op32 A v n = ops.op32 A v n := rfl
#print axioms op81_source
#print axioms op32_preserved
end R1Z.PV_CB_Heap
