import NEW_GeometryArithmetic
set_option autoImplicit false
namespace NEW_GeometryPolynomial
open Aeneas Aeneas.Std Result AspisR1

def native (x : U32) : Result U32 := do
 let p ← NEW_GeometryActual.aspis_core.field.M31.mul x x
 let d ← NEW_GeometryActual.aspis_core.field.M31.double p
 NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE

def cohort (x : U32) : Result U32 := do
 let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
 let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
 AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32

/-- Product canonicality discharges BOTH later scalar domains, on every raw input. -/
theorem complete (x : U32) : native x = cohort x := by
 obtain ⟨p,product,_,cp⟩ := ExtractedCurrentReducer.current_mul_mod x x
 obtain ⟨d,doubled,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod p p cp cp
 have doubleRun : AspisR1Qm31ArithmeticProbe.field.M31.double p=ok d := by
  simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using doubled
 simp only [native,cohort,NEW_GeometryArithmetic.multiply_probe,product,bind_tc_ok,
  NEW_GeometryArithmetic.double_probe p cp,doubleRun,
  NEW_GeometryActual.aspis_core.field.M31.ONE,
  NEW_GeometryArithmetic.sub_probe d 1#u32 cd (by decide)]

theorem continuation {T : Type} (x : U32) (k : U32 → Result T) :
 (do let p ← NEW_GeometryActual.aspis_core.field.M31.mul x x
     let d ← NEW_GeometryActual.aspis_core.field.M31.double p
     let z ← NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE
     k z) =
 (do let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
     let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
     let z ← AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32
     k z) := by
 have same := congrArg (fun r : Result U32 => do let z ← r; k z) (complete x)
 simpa only [native,cohort,bind_assoc_eq,bind_tc_ok] using same

#print axioms complete
#print axioms continuation
end NEW_GeometryPolynomial
