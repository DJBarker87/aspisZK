import NEW_GeometryArithmetic
import Port4C_NativePrefix
set_option autoImplicit false
namespace NEW_GeometryPrefix
open Aeneas Aeneas.Std Result AspisR1

def leaves : Port4C_NativePrefix.Leaves := ⟨AspisR1Qm31ArithmeticProbe.field.M31.mul,ok 1#u32⟩

theorem step (flat : Slice U32) (prefixes : alloc.vec.Vec U32) (product : U32) (index : Usize) :
    NEW_GeometryActual.verifier.batch_prefix_products_loop.body flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop.body leaves flat prefixes product index := by
  simp only [NEW_GeometryActual.verifier.batch_prefix_products_loop.body,
    Port4C_NativePrefix.verifier.batch_prefix_products_loop.body,leaves,
    NEW_GeometryArithmetic.multiply_probe]

theorem loop (flat : Slice U32) (prefixes : alloc.vec.Vec U32) (product : U32) (index : Usize) :
    NEW_GeometryActual.verifier.batch_prefix_products_loop flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop leaves flat prefixes product index := by
  unfold NEW_GeometryActual.verifier.batch_prefix_products_loop
    Port4C_NativePrefix.verifier.batch_prefix_products_loop
  simp only [step]

theorem complete (flat : Slice U32) : NEW_GeometryActual.verifier.batch_prefix_products flat =
    Port4C_NativePrefix.verifier.batch_prefix_products leaves flat := by
  simp only [NEW_GeometryActual.verifier.batch_prefix_products,
    Port4C_NativePrefix.verifier.batch_prefix_products,leaves,
    NEW_GeometryActual.aspis_core.field.M31.ONE,bind_tc_ok,loop]

#print axioms step
#print axioms loop
#print axioms complete
end NEW_GeometryPrefix
