import NEO_TailRef.Funs
import NEB_InverseCalls
import NEB_GeometryIndices
import Port4B_Opening
set_option autoImplicit false
namespace NEO_TailReference
open Aeneas Aeneas.Std Result AspisR1

def inverseOps : NEO_TailRef.InverseOps Unit where
 mul := FIo_Native.aspis_core.field.M31.mul
 square := AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul

/-- Exact independently extracted addition chain, including the zero panic. -/
theorem inverse (x : U32) :
 NEO_TailRef.inverse inverseOps x =
 AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x := rfl

/-- Exact independently extracted native opening range; arithmetic is release
wrapping in both definitions and bounds are proved by the existing caller. -/
theorem opening (proof : Slice U8) (i : Usize) :
 NEO_TailRef.opening proof i=Port4B_Opening.opening proof i := rfl

/-- The constructor Result is checked; no unchecked FibreIndex alias is used
as a constructor implementation. Mapping the one rejected value stays explicit. -/
theorem checked {C : Type} (error : C) (u : Usize) :
 NEB_GeometryIndices.indexPort error u =
 (do let r ← NEO_TailRef.checked u
     ok (match r with | .Ok x => .Ok x | .Err _ => .Err error)) := by
 simp only [NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref,NEO_TailRef.checked]

#print axioms inverse
#print axioms opening
#print axioms checked
end NEO_TailReference
