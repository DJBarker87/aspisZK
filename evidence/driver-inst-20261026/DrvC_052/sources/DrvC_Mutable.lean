import DrvC_FirstLibrary
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Mutable
open Aeneas Aeneas.Std Result
open Tx1Q_Carriers

theorem deref (a : C.A) : (accumulator a).weights.deref = slice k a.weights.deref := rfl

theorem deref_mut_current (a : C.A) : alloc.vec.Vec.deref_mut a.weights =
    (a.weights.deref,fun s : Slice C.K => (⟨s.val,s.property⟩ : alloc.vec.Vec C.K)) := rfl

theorem deref_mut_stage (a : S.A) : alloc.vec.Vec.deref_mut a.weights =
    (a.weights.deref,fun s : Slice S.K => (⟨s.val,s.property⟩ : alloc.vec.Vec S.K)) := rfl

theorem materialize (a : C.A) (s : Slice C.K) :
    {accumulator a with weights := ⟨(slice k s).val,(slice k s).property⟩} =
      accumulator {a with weights := ⟨s.val,s.property⟩} := rfl

#print axioms deref
#print axioms deref_mut_current
#print axioms deref_mut_stage
#print axioms materialize
end AspisR1.DrvC_Mutable
end
