import R1Z.PV_RunJoin_MaterialVec49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayVecImage49
open Aeneas Aeneas.Std ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
theorem complete {A B : Type} (n : Usize) (f : A → B) (a : Array A n)
    (v : alloc.vec.Vec B) (h : v.val=a.val.map f) :
    alloc.vec.Vec.deref v=Array.to_slice (amap f a) := by
  apply Subtype.ext
  exact h
#print axioms complete
end R1Z.PV_RunJoin_ArrayVecImage49
