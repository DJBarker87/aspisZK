import NFB_BackwardCongr
set_option autoImplicit false
noncomputable section
namespace NFB_BackwardTransport
open Aeneas Aeneas.Std AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary

theorem body (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body ops flat prefixes iter suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body adopted flat prefixes iter suffix inverse := by
 exact NFB_BackwardCongr.body ops adopted NFB_BackwardCongr.multiply flat prefixes iter suffix inverse

theorem complete (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0 iter flat prefixes suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 adopted iter flat prefixes suffix inverse := by
 rw [NEW_GeometryRawHelpers.backward]
 exact NFB_BackwardCongr.loop ops adopted NFB_BackwardCongr.multiply flat prefixes iter suffix inverse
#print axioms body
#print axioms complete
end NFB_BackwardTransport
end
