import FJi_DecodeCM31
import R1CandidateParserSupport
set_option autoImplicit false
namespace AspisR1.FJl_CMParser
open Aeneas Aeneas.Std Result
abbrev NC := FIo_FieldBridge.NC
def toCandidate (x : NC) : AspisR1CandidateParser.field.CM31 := ⟨x.a,x.b⟩
theorem m31 (a : Array U8 4#usize) :
    FIp_DotDecode.field.M31.from_le_bytes a=AspisR1CandidateParser.field.M31.from_le_bytes a := by
  simp only [FIp_DotDecode.field.M31.from_le_bytes,AspisR1CandidateParser.field.M31.from_le_bytes,
    FIp_DotDecode.field.P,AspisR1CandidateParser.field.P]
/-- Transport strict CM31 success with identical source byte subreads. -/
theorem source (bytes : Slice U8) (out : NC)
    (run : FIp_DotDecode.field.CM31.from_le_bytes bytes=ok (some out)) :
    AspisR1CandidateParser.field.CM31.from_le_bytes bytes=ok (some (toCandidate out)) := by
  unfold FIp_DotDecode.field.CM31.from_le_bytes at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok a0 =>
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
      | Ok a1 =>
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
          rw [m31] at ho ho1
          simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,hs,hr,ho,hs1,hr1,ho1,
            bind_tc_ok,CandidateParserSupport.branch_some,toCandidate]
#print axioms m31
#print axioms source
end AspisR1.FJl_CMParser
