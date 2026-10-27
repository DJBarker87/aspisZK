import FJc_Constructor
import FIo_FieldBridge
set_option autoImplicit false
namespace AspisR1.FJc_WeightScalarBridge
open Aeneas Aeneas.Std Result
namespace S := FIn_WeightsExtract.field
namespace N := FIo_Native.aspis_core.field

theorem add (x y : U32) : S.M31.add x y=N.M31.add x y := by
  unfold S.M31.add N.M31.add S.P N.P
  rfl
theorem sub (x y : U32) : S.M31.sub x y=N.M31.sub x y := by
  unfold S.M31.sub N.M31.sub S.P N.P
  rfl
theorem reduce (x : U64) : S.reduce_u64 x=N.reduce_u64 x := by
  unfold S.reduce_u64 N.reduce_u64 S.P N.P
  rfl
theorem mul (x y : U32) : S.M31.mul x y=N.M31.mul x y := by
  unfold S.M31.mul N.M31.mul
  simp only [reduce]
theorem double (x : U32) : S.M31.double x=N.M31.double x := by
  unfold S.M31.double N.M31.double
  exact add x x
#print axioms add
#print axioms sub
#print axioms reduce
#print axioms mul
#print axioms double
end AspisR1.FJc_WeightScalarBridge
