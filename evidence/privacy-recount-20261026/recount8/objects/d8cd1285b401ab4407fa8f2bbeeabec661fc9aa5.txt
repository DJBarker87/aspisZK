import R1Z.PV_CB_Heap
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op81Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op81_source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    (PV_CB_Heap.selected ops).op81 copy n value =
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ (PV_CB_Borrow.selected ops) T copy n value := rfl
#print axioms op81_source
end R1Z.PV_CB_Op81Source
