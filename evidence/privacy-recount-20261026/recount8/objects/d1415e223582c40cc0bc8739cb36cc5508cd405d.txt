import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op81Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Heap
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op81_source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    (selected ops).op81 copy n value =
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ (PV_CB_Borrow.selected (ProverRwP6BodyStore.selected ops)) T copy n value := by
  exact PV_CB_Op81Source.op81_source (ProverRwP6BodyStore.selected ops) copy n value
#print axioms op81_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Heap
