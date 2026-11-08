import NNH_Run5bGeometrySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryCallbacks
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody
open verifier.QueryGeometry.for_range
/-- Array gather's inner callback does not consult the operation dictionary. -/
theorem gather_inner {C D : Type} (g : Ops C) (h : Ops D) :
 closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 g =
 closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 h := rfl

theorem gather_outer {C D : Type} (g : Ops C) (h : Ops D)
 (array : @g.op0 = @h.op0) :
 closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g =
 closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 h := by
 unfold closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
  closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315
  closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once
  closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
 rw [array,gather_inner g h]

theorem zero_test {C D : Type} (g : Ops C) (h : Ops D)
 (zero : g.op6 = h.op6) (equal : ∀ x y, g.op5 x y = h.op5 x y) :
 closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool g =
 closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool h := by
 unfold closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
  closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool
  closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once
  closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
 simp only [zero,equal]
#print axioms gather_inner
#print axioms gather_outer
#print axioms zero_test
end AspisR1.NNV_GeometryCallbacks
end
