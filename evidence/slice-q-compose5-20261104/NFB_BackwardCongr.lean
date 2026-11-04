import NFB_ReverseAssociation
set_option autoImplicit false
noncomputable section
namespace NFB_BackwardCongr
open Aeneas Aeneas.Std AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary

theorem body {CE : Type} (a b : Port3_NativeGeometryBody.Ops CE)
 (multiply : a.op9=b.op9) (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body a flat prefixes iter suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body b flat prefixes iter suffix inverse := by
 simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body,multiply]

theorem loop {CE : Type} (a b : Port3_NativeGeometryBody.Ops CE)
 (multiply : a.op9=b.op9) (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 a iter flat prefixes suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 b iter flat prefixes suffix inverse := by
 unfold Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0
 simp only [body a b multiply]

theorem multiply : ops.op9=adopted.op9 := by
 change NEW_GeometryActual.aspis_core.field.M31.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul
 exact funext (fun x=>funext (NEW_GeometryArithmetic.multiply_probe x))
#print axioms body
#print axioms loop
#print axioms multiply
end NFB_BackwardCongr
end
