import R1Z.PV_RunJoin_PrefixFold50
import R1Z.PV_RunJoin_ArrayVecImage49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PrefixImage50
open Aeneas Aeneas.Std
open PV_B2_F_ConstructorCarrier (amap)

theorem length {A B : Type} (f : A → B) (a : Array A 1024#usize) :
    (PV_RunJoin_PrefixFold50.image f a).length=1024 := by
  change (a.val.map f).length=1024
  rw [List.length_map,a.property]
  rfl

theorem slice {A B : Type} (f : A → B) (a : Array A 1024#usize) :
    alloc.vec.Vec.deref (PV_RunJoin_PrefixFold50.image f a)=Array.to_slice (amap f a) := by
  apply Subtype.ext
  rfl

theorem material (a : Array PV_RunJoin_MaterialVec49.S 1024#usize) :
    PV_RunJoin_MaterialVec49.vec a=PV_RunJoin_PrefixFold50.image ProverRwDictionaryTower.fromW a := rfl
#print axioms length
#print axioms slice
#print axioms material
end R1Z.PV_RunJoin_PrefixImage50
