import FJa_SquareValue
import FIo_M31Values
import ExtractedCurrentReducer
import ExtractedMaskReducer
set_option autoImplicit false
namespace AspisR1.FJm_MaskScalarBridge
open Aeneas Aeneas.Std Result

theorem reduce (x : U64) : FIo_Native.aspis_core.field.M31.reduce_u64 x=
    AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  have native : FIo_Native.aspis_core.field.M31.reduce_u64 x=
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64,FIo_ReduceBridge.same,
      AspisR1CurrentWide.Proof.reduce_same]
  obtain ⟨a,ha,va,ca⟩ := ExtractedCurrentReducer.current_wrapper_mod x
  obtain ⟨b,hb,vb,cb⟩ := ExtractedMaskReducer.current_wrapper_mod x
  have eq : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [native,ha,hb,eq]

theorem mul (x y : U32) : FIo_Native.aspis_core.field.M31.mul x y=
    AspisR1SelectedMaskProbe.field.M31.mul x y := by
  obtain ⟨a,ha,va,ca⟩ := ExtractedCurrentReducer.current_mul_mod x y
  obtain ⟨b,hb,vb,cb⟩ := ExtractedMaskReducer.current_mul_mod x y
  have eq : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [FIo_M31MulBridge.same,AspisR1CurrentWide.Proof.m31_mul_same,ha,hb,eq]

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1SelectedMaskProbe.field.M31.add x y := by
  obtain ⟨a,ha,va,ca⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  obtain ⟨b,hb,vb,cb⟩ := ExtractedMaskM31AddSub.current_add_mod x y hx hy
  have eq : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [FIo_M31Bridge.add x y hx hy,AspisR1CurrentWide.Proof.m31_add_same,ha,hb,eq]
#print axioms reduce
#print axioms mul
#print axioms add
end AspisR1.FJm_MaskScalarBridge
