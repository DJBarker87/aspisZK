import NEW_GeometryDictionary
set_option autoImplicit false
noncomputable section
namespace NEW_GeometryContext
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryRawBody NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20


theorem reverse (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (flat pref : alloc.vec.Vec U32) (suffix : U32) (inv : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 contextual it flat pref suffix inv =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 adopted it flat pref suffix inv := by rfl

theorem zero_callback :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool contextual =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool adopted := by rfl

theorem collect_callback :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 contextual =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 adopted := by rfl

theorem one : adopted.op7=ok 1#u32 := by rfl
 theorem multiply : adopted.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by rfl
 theorem double : adopted.op10=AspisR1Qm31ArithmeticProbe.field.M31.double := by rfl
 theorem subtract : adopted.op8=AspisR1Qm31ArithmeticProbe.field.M31.sub := by rfl

theorem polynomial {T : Type} (x : U32) (k : U32 → Result T) :
 (do let p ← adopted.op9 x x
     let d ← ops.op10 p
     let one ← adopted.op7
     let z ← ops.op8 d one
     k z) =
 (do let p ← adopted.op9 x x
     let d ← adopted.op10 p
     let one ← adopted.op7
     let z ← adopted.op8 d one
     k z) := by
 simp only [one,multiply,double,subtract,ops,bind_tc_ok]
 simpa only [NEW_GeometryArithmetic.multiply_probe] using NEW_GeometryPolynomial.continuation x k

/-- Contextual replacement of only the two operations whose unrestricted raw
input specifications differ. The preceding product establishes their domains. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body contextual start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,reverse,zero_callback,collect_callback]
  simp only [contextual,bind_assoc_eq,bind_tc_ok]
  repeat' first
  | rfl
  | simp only [uncurry,bind_assoc_eq,bind_tc_ok,polynomial]
  | (apply bind_congr; intro)
  | split

#print axioms reverse
#print axioms zero_callback
#print axioms collect_callback
#print axioms one
#print axioms multiply
#print axioms double
#print axioms subtract
#print axioms polynomial
#print axioms step
end NEW_GeometryContext
end
