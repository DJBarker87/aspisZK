import RPu_FIr_NativeArithmetic
import RPt_FIo_M31Values
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeScalar
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof

theorem sub_same (x y : U32) : FIq_Native.field.M31.sub x y=
    AspisR1CurrentWide.field.M31.sub x y := by
  simp only [FIq_Native.field.M31.sub,AspisR1CurrentWide.field.M31.sub,
    FIq_Native.field.P,AspisR1CurrentWide.field.P]

theorem sub (x y z : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
    (run : FIq_Native.field.M31.sub x y=ok z) :
    z.val<2147483647 ∧ decodeM z=decodeM x-decodeM y := by
  have hc : AspisR1CurrentWide.field.M31.sub x y=ok z := by rw [← sub_same];exact run
  have value := m31_sub_exact x y z hc
  rw [m31_sub_same] at hc
  exact ⟨R17CurrentDomainCanonical.sub_success_canonical x y z hx hy hc,value⟩

#print axioms sub_same
#print axioms sub
end AspisR1.FIr_NativeScalar
end
