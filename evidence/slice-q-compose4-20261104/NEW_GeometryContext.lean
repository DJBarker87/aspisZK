import NEW_GeometryDictionary
import NEW_GeometryContextGeneric
set_option autoImplicit false
noncomputable section
namespace NEW_GeometryContext
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryRawBody NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20


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
 simpa only [NEW_GeometryArithmetic.multiply_probe,NEW_GeometryActual.aspis_core.field.M31.ONE] using NEW_GeometryPolynomial.continuation x k

/-- Contextual replacement of only the two operations whose unrestricted raw
input specifications differ. The preceding product establishes their domains. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body contextual start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  exact NEW_GeometryContextGeneric.step adopted ops.op8 ops.op10
    (fun T x k => polynomial x k) start iter lines flat

#print axioms one
#print axioms multiply
#print axioms double
#print axioms subtract
#print axioms polynomial
#print axioms step
end NEW_GeometryContext
end
