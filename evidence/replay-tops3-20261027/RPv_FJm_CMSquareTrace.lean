import RPv_FJm_CMSquareOperandJoin
import RPv_FJm_SquareOperand
set_option autoImplicit false
namespace AspisR1.FJm_CMSquareTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NC)

theorem reached (x out : NC) (run : FIo_Native.aspis_core.field.CM31.square x=ok out) :
    ∃ (real ab imag : U32),
      FIo_Native.aspis_core.field.M31.reduce_u64 (FJm_SquareOperand.operand x.a x.b)=ok real ∧
      FIo_Native.aspis_core.field.M31.mul x.a x.b=ok ab ∧
      FIo_Native.aspis_core.field.M31.double ab=ok imag ∧ out=⟨real,imag⟩ := by
  obtain ⟨i1,i3,i4,i5,i6,i7,i8,i9,i10,real,ab,imag,h1,h3,h4,h5,h6,h7,h8,h9,h10,hr,hab,hi,hout⟩ :=
    FJm_CMSquareRawTrace.reached x out run
  have joined := FJm_CMSquareOperandJoin.value x i1 i3 i4 i5 i6 i7 i8 i9 i10 h1 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨real,ab,imag,by rw [joined];exact hr,hab,hi,hout⟩
#print axioms reached
end AspisR1.FJm_CMSquareTrace
