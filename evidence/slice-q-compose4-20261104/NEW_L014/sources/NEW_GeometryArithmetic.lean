import NEW_GeometryActual.Funs
import NEW_InverseAssociation
import NEB_GeometryFieldPorts
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
namespace NEW_GeometryArithmetic
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev C := NEW_GeometryActual.aspis_core.field.CM31
abbrev NC := FIo_Native.aspis_core.field.CM31

def toC (x : C) : NC := ⟨x.a,x.b⟩
def fromC (x : NC) : C := ⟨x.a,x.b⟩

theorem roundtrip (x : C) : fromC (toC x)=x := by cases x; rfl

theorem reducer (x : U64) : NEW_GeometryActual.aspis_core.field.reduce_u64 x =
    FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [NEW_GeometryActual.aspis_core.field.reduce_u64,
    FIo_Native.aspis_core.field.reduce_u64,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem multiply (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.mul x y =
    FIo_Native.aspis_core.field.M31.mul x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.mul,
    FIo_Native.aspis_core.field.M31.mul,reducer]

theorem reduce_wrapper (x : U64) : NEW_GeometryActual.aspis_core.field.M31.reduce_u64 x =
    FIo_Native.aspis_core.field.M31.reduce_u64 x := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.reduce_u64,
    FIo_Native.aspis_core.field.M31.reduce_u64,reducer]

theorem add (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.add x y =
    FIo_Native.aspis_core.field.M31.add x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.add,
    FIo_Native.aspis_core.field.M31.add,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem sub (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.sub x y =
    FIo_Native.aspis_core.field.M31.sub x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.sub,
    FIo_Native.aspis_core.field.M31.sub,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem double (x : U32) : NEW_GeometryActual.aspis_core.field.M31.double x =
    FIo_Native.aspis_core.field.M31.double x := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.double,
    FIo_Native.aspis_core.field.M31.double,add]

theorem multiply_probe (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.mul x y =
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y :=
  (multiply x y).trans (NBG_InverseBridge.mul_eq_probe x y)

theorem double_probe (x : U32) (hx : x.val<2147483647) :
    NEW_GeometryActual.aspis_core.field.M31.double x =
      AspisR1Qm31ArithmeticProbe.field.M31.double x :=
  (double x).trans (NEB_GeometryFieldPorts.double x hx)

theorem sub_probe (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    NEW_GeometryActual.aspis_core.field.M31.sub x y =
      AspisR1Qm31ArithmeticProbe.field.M31.sub x y :=
  (sub x y).trans (NEB_GeometryFieldPorts.sub x y hx hy)

theorem square_body (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_GeometryActual.aspis_core.field.square_n_loop.body iter x =
      NEW_InverseActual.aspis_core.field.square_n_loop.body iter x := by
  simp only [NEW_GeometryActual.aspis_core.field.square_n_loop.body,
    NEW_InverseActual.aspis_core.field.square_n_loop.body,multiply,NEW_InverseAssociation.multiply]
  rfl

theorem square_loop (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_GeometryActual.aspis_core.field.square_n_loop iter x =
      NEW_InverseActual.aspis_core.field.square_n_loop iter x := by
  unfold NEW_GeometryActual.aspis_core.field.square_n_loop
    NEW_InverseActual.aspis_core.field.square_n_loop
  simp only [square_body]

theorem square (x : U32) (n : Usize) :
    NEW_GeometryActual.aspis_core.field.square_n x n =
      NEW_InverseActual.aspis_core.field.square_n x n := by
  simp only [NEW_GeometryActual.aspis_core.field.square_n,
    NEW_InverseActual.aspis_core.field.square_n,square_loop]

theorem inverse (x : U32) : NEW_GeometryActual.aspis_core.field.M31.inv x =
    Port4C_InverseExecution.inverse_owned x := by
  rw [←NEW_InverseAssociation.cohort]
  simp only [NEW_GeometryActual.aspis_core.field.M31.inv,
    NEW_InverseActual.aspis_core.field.M31.inv,multiply,NEW_InverseAssociation.multiply,square]

/-- Nominal record transport only; the existing arithmetic/domain proofs are reused. -/
theorem cm_multiply (x y : C) :
    resultMap toC (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
      FIo_Native.aspis_core.field.CM31.mul (toC x) (toC y) := by
  simp only [NEW_GeometryActual.aspis_core.field.CM31.mul,
    FIo_Native.aspis_core.field.CM31.mul,resultMap_bind,multiply,reduce_wrapper,sub,
    toC,resultMap]

#print axioms roundtrip
#print axioms reducer
#print axioms multiply
#print axioms reduce_wrapper
#print axioms add
#print axioms sub
#print axioms double
#print axioms multiply_probe
#print axioms double_probe
#print axioms sub_probe
#print axioms square_body
#print axioms square_loop
#print axioms square
#print axioms inverse
#print axioms cm_multiply
end NEW_GeometryArithmetic
