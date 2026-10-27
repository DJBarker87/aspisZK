import FJm_SquareOperand
import FJm_BaseCast
import FJm_ModSquare
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_RealSquare
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof

theorem value (a b out : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
    (run : FIo_Native.aspis_core.field.M31.reduce_u64 (FJm_SquareOperand.operand a b)=ok out) :
    out.val<2147483647 ∧ decodeM out=decodeM a*decodeM a+(-1)*decodeM b*decodeM b := by
  obtain ⟨product,hchecked,hoperand,numeric⟩ := FJm_SquareOperand.value a b ha hb
  rw [hoperand] at run
  have vr := FIo_ReduceValues.field_value product out run
  have cr := (FIo_ReduceValues.m31_value product out run).2
  have castValue := congrArg (fun n : Nat=>(n : ZMod 2147483647)) numeric
  have modular := FJm_ModSquare.value 2147483647 a.val b.val (by omega)
  rw [FJm_BaseCast.value,FJm_BaseCast.value] at modular
  exact ⟨cr,vr.trans (castValue.trans modular)⟩
#print axioms value
end AspisR1.FJm_RealSquare
end
