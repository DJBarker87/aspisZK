import RPu_FJi_DecodeCM31
import RPt_FIo_QMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_DecodeQM31
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
theorem canonical (bytes : Slice U8) (out : NQ)
    (run : FIp_DotDecode.field.QM31.from_le_bytes bytes=ok (some out)) :
    FIo_QMValues.Canon out := by
  unfold FIp_DotDecode.field.QM31.from_le_bytes at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
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
      exact ⟨FJi_DecodeCM31.canonical s a ho,FJi_DecodeCM31.canonical s1 b ho1⟩
#print axioms canonical
end AspisR1.FJi_DecodeQM31
end
