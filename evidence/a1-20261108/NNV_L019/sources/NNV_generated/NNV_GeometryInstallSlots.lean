import NNH_Run5bGeometryUnits
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryInstallSlots
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
abbrev installed {C : Type} (base : Ops C) :=
 Port5Q1_GeometryTerminal.install base
/-- Named abstract installation projections replace the retired concrete rfl comparisons. -/
theorem array {C : Type} (base : Ops C) :
 @(installed base).op0 = @OraclePortStdBuilder.fromFn := rfl
theorem iterator {C : Type} (base : Ops C) :
 @(installed base).op1 = @OraclePortStdBuilder.iterMap := rfl
theorem mapped {C : Type} (base : Ops C) :
 @(installed base).mapIterator = @Port4C_CollectStd.mapIterator := rfl
theorem any {C : Type} (base : Ops C) {T F : Type}
 (pred : core.ops.function.FnMut F T Bool) (it : core.slice.iter.Iter T) (f : F) :
 (installed base).op3 pred it f =
 Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T) pred it f := rfl
theorem empty {C : Type} (base : Ops C) (T : Type) (a : alloc.vec.Vec T) :
 (installed base).op4 Global a = .ok a.val.isEmpty := rfl
theorem zero {C : Type} (base : Ops C) :
 (installed base).op6 = .ok (0#u32) := rfl
#print axioms array
#print axioms iterator
#print axioms mapped
#print axioms any
#print axioms empty
#print axioms zero
end AspisR1.NNV_GeometryInstallSlots
end
