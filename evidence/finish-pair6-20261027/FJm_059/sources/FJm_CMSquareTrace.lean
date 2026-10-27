import FJm_SquareOperand
set_option autoImplicit false
namespace AspisR1.FJm_CMSquareTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NC)

theorem reached (x out : NC) (run : FIo_Native.aspis_core.field.CM31.square x=ok out) :
    ∃ (real ab imag : U32),
      FIo_Native.aspis_core.field.M31.reduce_u64 (FJm_SquareOperand.operand x.a x.b)=ok real ∧
      FIo_Native.aspis_core.field.M31.mul x.a x.b=ok ab ∧
      FIo_Native.aspis_core.field.M31.double ab=ok imag ∧ out=⟨real,imag⟩ := by
  change (do
    let real ← FIo_Native.aspis_core.field.M31.reduce_u64 (FJm_SquareOperand.operand x.a x.b)
    let ab ← FIo_Native.aspis_core.field.M31.mul x.a x.b
    let imag ← FIo_Native.aspis_core.field.M31.double ab
    ok (⟨real,imag⟩ : NC))=ok out at run
  obtain ⟨real,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ab,hab,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨imag,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨real,ab,imag,hr,hab,hi,(Result.ok.inj run).symm⟩
#print axioms reached
end AspisR1.FJm_CMSquareTrace
