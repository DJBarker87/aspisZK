import NEW_InverseActual.Funs
import NET_MultiplyBridge
set_option autoImplicit false
namespace NEW_InverseAssociation
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- Literal frozen-source reducer: no additional arithmetic proof or input restriction. -/
theorem reducer (x : U64) :
    NEW_InverseActual.aspis_core.field.reduce_u64 x =
      FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [NEW_InverseActual.aspis_core.field.reduce_u64,
    FIo_Native.aspis_core.field.reduce_u64,
    NEW_InverseActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem multiply (x y : U32) :
    NEW_InverseActual.aspis_core.field.M31.mul x y =
      FIo_Native.aspis_core.field.M31.mul x y := by
  simp only [NEW_InverseActual.aspis_core.field.M31.mul,
    FIo_Native.aspis_core.field.M31.mul,reducer]

/-- One actual native square-loop body, with the same iterator and field word. -/
theorem square_body (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_InverseActual.aspis_core.field.square_n_loop.body iter x =
      AspisR1M31Inverse.field.square_n_loop.body
        FIo_Native.aspis_core.field.M31.mul iter x := by
  simp only [NEW_InverseActual.aspis_core.field.square_n_loop.body,
    AspisR1M31Inverse.field.square_n_loop.body,multiply]

/-- Generic loop association follows from equality of the step functions;
there is no concrete recurrence unfolding and no count bound. -/
theorem square_loop (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_InverseActual.aspis_core.field.square_n_loop iter x =
      AspisR1M31Inverse.field.square_n_loop
        FIo_Native.aspis_core.field.M31.mul iter x := by
  unfold NEW_InverseActual.aspis_core.field.square_n_loop
    AspisR1M31Inverse.field.square_n_loop
  simp only [square_body]

theorem square (x : U32) (n : Usize) :
    NEW_InverseActual.aspis_core.field.square_n x n =
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul x n := by
  simp only [NEW_InverseActual.aspis_core.field.square_n,
    AspisR1M31Inverse.field.square_n,square_loop]

/-- Entire actual extracted inverse Result, including the zero assertion.
All raw U32 words are included; no caller output or nonzero premise. -/
theorem emitted (x : U32) :
    NEW_InverseActual.aspis_core.field.M31.inv x =
      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x := by
  simp only [NEW_InverseActual.aspis_core.field.M31.inv,
    AspisR1M31Inverse.field.M31.inv,multiply,square]

theorem cohort (x : U32) :
    NEW_InverseActual.aspis_core.field.M31.inv x =
      Port4C_InverseExecution.inverse_owned x :=
  (emitted x).trans (NBG_InverseBridge.inverse_result x)

theorem zero : NEW_InverseActual.aspis_core.field.M31.inv 0#u32 =
    fail .assertionFailure := by
  simp [NEW_InverseActual.aspis_core.field.M31.inv,massert]

#print axioms reducer
#print axioms multiply
#print axioms square_body
#print axioms square_loop
#print axioms square
#print axioms emitted
#print axioms cohort
#print axioms zero
#print axioms NEW_InverseActual.aspis_core.field.M31.inv
end NEW_InverseAssociation
