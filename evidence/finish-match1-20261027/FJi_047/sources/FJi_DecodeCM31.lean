import FJi_DecodeM31
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_DecodeCM31
open Aeneas Aeneas.Std Result
abbrev NC := FIo_FieldBridge.NC
/-- Successful installed decoder enforces BOTH canonical limb guards. -/
theorem canonical (bytes : Slice U8) (out : NC)
    (run : FIp_DotDecode.field.CM31.from_le_bytes bytes=ok (some out)) :
    out.a.val < 2147483647 ∧ out.b.val < 2147483647 := by
  unfold FIp_DotDecode.field.CM31.from_le_bytes at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok b0 =>
    obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases o with
    | none =>
      simp only [FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok,
        FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases run
    | some a =>
      simp only [FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok] at run
      obtain ⟨s1,hs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨r1,hr1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases r1 with
      | Err e => cases run
      | Ok b1 =>
        obtain ⟨o1,ho1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases o1 with
        | none =>
          simp only [FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok,
            FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at run
          obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
          cases run
        | some b =>
          simp only [FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok] at run
          cases Option.some.inj (Result.ok.inj run)
          exact ⟨(FJi_DecodeM31.value b0 a ho).2,(FJi_DecodeM31.value b1 b ho1).2⟩
#print axioms canonical
end AspisR1.FJi_DecodeCM31
end
