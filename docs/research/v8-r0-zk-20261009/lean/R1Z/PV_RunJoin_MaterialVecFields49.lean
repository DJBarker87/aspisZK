import R1Z.PV_RunJoin_ArrayVecImage49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialVecFields49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_MaterialVec49 (S vec)

theorem value (a : Array S 1024#usize) :
    (vec a).val=a.val.map ProverRwDictionaryTower.fromW := rfl

theorem slice (a : Array S 1024#usize) :
    alloc.vec.Vec.deref (vec a)=Array.to_slice (PV_B2_F_ConstructorCarrier.amap ProverRwDictionaryTower.fromW a) :=
  PV_RunJoin_ArrayVecImage49.complete _ _ a _ (value a)
#print axioms value
#print axioms slice
end R1Z.PV_RunJoin_MaterialVecFields49
