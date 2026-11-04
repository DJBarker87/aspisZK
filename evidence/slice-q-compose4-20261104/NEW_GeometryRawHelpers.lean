import NEW_GeometryRawInterface
import NEW_LoopMap
set_option autoImplicit false
namespace NEW_GeometryRawHelpers
open Aeneas Aeneas.Std Result AspisR1 NEW_GeometryRawInterface

theorem zero_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops := by rfl

theorem inner_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 ops := by rfl

theorem outer_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops := by rfl

theorem clone : NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone =
    core.marker.CopyU32.cloneInst := by rfl

theorem backward_body (flat prefixes : alloc.vec.Vec U32)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (suffix : U32) (inverse : alloc.vec.Vec U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0.body flat prefixes iter suffix inverse =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body
        ops flat prefixes iter suffix inverse := by rfl

theorem backward (flat prefixes : alloc.vec.Vec U32)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (suffix : U32) (inverse : alloc.vec.Vec U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0 iter flat prefixes suffix inverse =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0
        ops iter flat prefixes suffix inverse := by rfl

#print axioms zero_callback
#print axioms inner_callback
#print axioms outer_callback
#print axioms clone
#print axioms backward_body
#print axioms backward
end NEW_GeometryRawHelpers
