import RPv_FJm_SquareOperand
set_option autoImplicit false
namespace AspisR1.FJm_CMSquareRawTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NC)
abbrev widen := core.convert.num.FromU64U32.from

theorem reached (x out : NC) (run : FIo_Native.aspis_core.field.CM31.square x=ok out) :
    ∃ (i1 i3 i4 i5 i6 i7 i8 i9 i10 : U64) (real ab imag : U32),
      lift (widen x.a)=ok i1 ∧ lift (widen x.b)=ok i3 ∧
      lift (U64.wrapping_add i1 i3)=ok i4 ∧ lift (widen x.a)=ok i5 ∧
      lift (widen FIo_Native.aspis_core.field.P)=ok i6 ∧
      lift (U64.wrapping_add i5 i6)=ok i7 ∧ lift (widen x.b)=ok i8 ∧
      lift (U64.wrapping_sub i7 i8)=ok i9 ∧ lift (U64.wrapping_mul i4 i9)=ok i10 ∧
      FIo_Native.aspis_core.field.M31.reduce_u64 i10=ok real ∧
      FIo_Native.aspis_core.field.M31.mul x.a x.b=ok ab ∧
      FIo_Native.aspis_core.field.M31.double ab=ok imag ∧ out=⟨real,imag⟩ := by
  unfold FIo_Native.aspis_core.field.CM31.square at run
  obtain ⟨i1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i4,h4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i5,h5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i6,h6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i7,h7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i8,h8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i9,h9,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i10,h10,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨real,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ab,hab,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨imag,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨i1,i3,i4,i5,i6,i7,i8,i9,i10,real,ab,imag,h1,h3,h4,h5,h6,h7,h8,h9,h10,hr,hab,hi,(Result.ok.inj run).symm⟩
#print axioms reached
end AspisR1.FJm_CMSquareRawTrace
