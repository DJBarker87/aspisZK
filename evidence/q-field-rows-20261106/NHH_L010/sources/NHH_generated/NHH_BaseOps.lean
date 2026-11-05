import NFG_InverseRef.Funs
import NGH_QSquareOps
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace NHH_BaseOps
open Aeneas Aeneas.Std Result AspisR1

theorem mul_probe (x y : U32) :
 NFG_InverseRef.field.M31.mul x y=AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
 simp only [NFG_InverseRef.field.M31.mul,NFG_InverseRef.field.reduce_u64,
  NFG_InverseRef.field.P,AspisR1Qm31ArithmeticProbe.field.M31.mul,
  AspisR1Qm31ArithmeticProbe.field.reduce_u64,AspisR1Qm31ArithmeticProbe.field.P]

theorem mul_native (x y : U32) :
 NFG_InverseRef.field.M31.mul x y=FIo_Native.aspis_core.field.M31.mul x y := (mul_probe x y).trans (NFN_NBG_InverseBridge.mul_eq_probe x y).symm


theorem mul_value (x y : U32) : ∃ out,
 NFG_InverseRef.field.M31.mul x y=ok out ∧
 out.val=(x.val*y.val)%2147483647 ∧ out.val<2147483647 := by
 obtain ⟨out,ho,hv,hc⟩ := AspisR1.NFN_LPf_BaseMultiply.source x y
 exact ⟨out,(mul_native x y).trans ho,hv,hc⟩

theorem square_body (i : core.ops.range.Range Usize) (x : U32) :
 NFG_InverseRef.field.square_n_loop.body i x=
 AspisR1M31Inverse.field.square_n_loop.body AspisR1Qm31ArithmeticProbe.field.M31.mul i x := by
 simp only [NFG_InverseRef.field.square_n_loop.body,AspisR1M31Inverse.field.square_n_loop.body,mul_probe]
 rfl

theorem square_chain (x : U32) (count : Usize) :
 NFG_InverseRef.field.square_n x count=
 AspisR1M31Inverse.field.square_n AspisR1Qm31ArithmeticProbe.field.M31.mul x count := by
 simp only [NFG_InverseRef.field.square_n,NFG_InverseRef.field.square_n_loop,
 AspisR1M31Inverse.field.square_n,AspisR1M31Inverse.field.square_n_loop,square_body]

theorem inverse_chain (x : U32) :
 NFG_InverseRef.field.M31.inv x=Port4C_InverseExecution.inverse_owned x := by
 have same : NFG_InverseRef.field.M31.inv x=AspisR1.SAQ_Inverse.source x := by
  simp only [AspisR1.SAQ_Inverse.source,NFG_InverseRef.field.M31.inv,AspisR1M31Inverse.field.M31.inv,mul_probe,square_chain]
 exact same.trans (congrFun AspisR1.SAQ_Inverse.source_eq_reference x)

#print axioms mul_probe
#print axioms mul_native
#print axioms mul_value
#print axioms square_body
#print axioms square_chain
#print axioms inverse_chain
end NHH_BaseOps
end
