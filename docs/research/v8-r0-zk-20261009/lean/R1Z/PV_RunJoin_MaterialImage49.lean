import R1Z.PV_RunJoin_MaterialVecFields49
import R1Z.PV_RunJoin_MaterialArray49
import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialImage49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48

theorem complete (w : Nat → Raw) :
    alloc.vec.Vec.deref (PV_RunJoin_MaterialVec49.vec (sourceArray 1024#usize w))=
      Array.to_slice (PV_RunJoin_FoldCell44.array 1024#usize w) := by
  trans Array.to_slice (PV_B2_F_ConstructorCarrier.amap ProverRwDictionaryTower.fromW (sourceArray 1024#usize w))
  · exact PV_RunJoin_MaterialVecFields49.slice (sourceArray 1024#usize w)
  · have equation := PV_RunJoin_MaterialArray49.maps 1024#usize w
    exact congrArg (fun a : Array aspis_core.field.wide_exact.WideExact 1024#usize => Array.to_slice a) equation
#print axioms complete
end R1Z.PV_RunJoin_MaterialImage49
