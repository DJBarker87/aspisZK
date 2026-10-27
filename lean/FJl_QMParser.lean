import FJl_CMParser
import R1CandidateStrictQM31Parser
set_option autoImplicit false
namespace AspisR1.FJl_QMParser
open Aeneas Aeneas.Std Result
abbrev NQ := FIo_FieldBridge.NQ
def toCandidate (x : NQ) : AspisR1CandidateParser.field.QM31 :=
  ⟨FJl_CMParser.toCandidate x.c0,FJl_CMParser.toCandidate x.c1⟩
/-- Transport strict QM31 success on the SAME input bytes and four raw limbs. -/
theorem source (bytes : Slice U8) (out : NQ)
    (run : FIp_DotDecode.field.QM31.from_le_bytes bytes=ok (some out)) :
    AspisR1CandidateParser.field.QM31.from_le_bytes bytes=ok (some (toCandidate out)) := by
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
      have ha := FJl_CMParser.source s a ho
      have hb := FJl_CMParser.source s1 b ho1
      simp only [AspisR1CandidateParser.field.QM31.from_le_bytes,hs,hs1,ha,hb,bind_tc_ok,
        CandidateParserSupport.branch_some,toCandidate]
#print axioms source
end AspisR1.FJl_QMParser
