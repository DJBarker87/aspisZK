import NBG_SquareLoop
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace NBG_InverseBridge
open Aeneas Aeneas.Std Result AspisR1

theorem mul_eq_probe (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y =
      AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
  obtain ⟨a,ha,va,_⟩ := LPf_BaseMultiply.source x y
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentReducer.current_mul_mod x y
  have same : a = b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

/-- Full raw-word Result, including the zero assertion and noncanonical
representations. No nonzero or successful-return premise is supplied. -/
theorem inverse_result (x : U32) :
    AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x =
      Port4C_InverseExecution.inverse_owned x := by
  have same : FIo_Native.aspis_core.field.M31.mul =
      AspisR1Qm31ArithmeticProbe.field.M31.mul := funext (fun a => funext (mul_eq_probe a))
  rw [same]
  change SAQ_Inverse.source x = Port4C_InverseExecution.inverse_owned x
  exact congrFun SAQ_Inverse.source_eq_reference x

#print axioms mul_eq_probe
#print axioms inverse_result
end NBG_InverseBridge
