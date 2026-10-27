import RPt_FJc_Constructor
import RPt_FIo_FieldBridge
set_option autoImplicit false
namespace AspisR1.FJc_WeightScalarBridge
open Aeneas Aeneas.Std Result

theorem add (x y : U32) : FIn_WeightsExtract.field.M31.add x y=FIo_Native.aspis_core.field.M31.add x y := by
  unfold FIn_WeightsExtract.field.M31.add FIo_Native.aspis_core.field.M31.add FIn_WeightsExtract.field.P FIo_Native.aspis_core.field.P
  rfl
theorem sub (x y : U32) : FIn_WeightsExtract.field.M31.sub x y=FIo_Native.aspis_core.field.M31.sub x y := by
  unfold FIn_WeightsExtract.field.M31.sub FIo_Native.aspis_core.field.M31.sub FIn_WeightsExtract.field.P FIo_Native.aspis_core.field.P
  rfl
theorem reduce (x : U64) : FIn_WeightsExtract.field.reduce_u64 x=FIo_Native.aspis_core.field.reduce_u64 x := by
  unfold FIn_WeightsExtract.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64 FIn_WeightsExtract.field.P FIo_Native.aspis_core.field.P
  rfl
theorem mul (x y : U32) : FIn_WeightsExtract.field.M31.mul x y=FIo_Native.aspis_core.field.M31.mul x y := by
  unfold FIn_WeightsExtract.field.M31.mul FIo_Native.aspis_core.field.M31.mul
  simp only [reduce]
theorem double (x : U32) : FIn_WeightsExtract.field.M31.double x=FIo_Native.aspis_core.field.M31.double x := by
  unfold FIn_WeightsExtract.field.M31.double FIo_Native.aspis_core.field.M31.double
  exact add x x
#print axioms add
#print axioms sub
#print axioms reduce
#print axioms mul
#print axioms double
end AspisR1.FJc_WeightScalarBridge
