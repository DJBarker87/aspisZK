import RPz7_Tx2I_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Writeback
open Aeneas Aeneas.Std Result AspisR1Stage2

def value (a : verifier.Accumulator) (flushed : Slice aspis_core.field.QM31) : verifier.Accumulator :=
  {a with weights := (alloc.vec.Vec.deref_mut a.weights).2 flushed}

theorem weights (a : verifier.Accumulator) (flushed : Slice aspis_core.field.QM31) :
    (value a flushed).weights.deref=flushed := rfl
#print axioms weights

theorem rhs (a : verifier.Accumulator) (flushed : Slice aspis_core.field.QM31) :
    (value a flushed).rhs=a.rhs := rfl
#print axioms rhs

theorem next (a : verifier.Accumulator) (flushed : Slice aspis_core.field.QM31) :
    (value a flushed).next=a.next := rfl
#print axioms next
end AspisR1.JGx_Writeback
end
