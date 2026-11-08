import NNH_Run5bGeometryReverse
import NNH_Run5bGeometryMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryCallbacks
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody

theorem inner {C C' : Type} (g : Ops C) (h : Ops C') :
 verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 g =
 verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 h := rfl

theorem gather {C C' : Type} (g : Ops C) (h : Ops C') (fromFn : @g.op0 = @h.op0) :
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g =
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 h := by
 simp only [verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315,
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315,
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once,
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut,
 fromFn,inner g h]

theorem zero {C C' : Type} (g : Ops C) (h : Ops C')
 (zero : g.op6=h.op6) (eq : g.op5=h.op5) :
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool g =
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool h := by
 simp only [verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool,
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool,
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once,
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut,
 zero,eq]
#print axioms inner
#print axioms gather
#print axioms zero
end AspisR1.NNU_GeometryCallbacks
end
