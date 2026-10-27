import R1Z.ProverRwSuccessHeapSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessHeapInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  letI : ExternalFuns := ProverRwSuccessBodyInterpretation.selected ops
  {ProverRwSuccessBodyInterpretation.selected ops with
    op81 := ProverRwSuccessHeapSource.aspis_core.r0.heap.filled}

theorem source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    (selected ops).op81 copy n value =
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _
        (ProverRwSuccessBodyInterpretation.selected ops) T copy n value := rfl
-- The allocator entry is deliberately not supplied by a success assumption.
theorem allocator_preserved (ops : ExternalFuns) (T A : Type)
    (v : alloc.vec.Vec T) (n : Usize) :
    (selected ops).op32 A v n = (ProverRwSuccessBodyInterpretation.selected ops).op32 A v n := rfl
#print axioms source
#print axioms allocator_preserved
end R1Z.ProverRwSuccessHeapInstall
