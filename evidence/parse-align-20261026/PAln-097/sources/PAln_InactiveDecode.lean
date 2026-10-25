import PAln_Physical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_InactiveDecode
open MultiproofConeCanonical OraclePortCompactDraft AspisR1SelectedWideViewV1

theorem parser (input : Slice U8) (out : aspis_core.field.wide_exact.WideExact)
    (accepted : viewFromBytes input=ok (some out)) :
    ∃ value : AspisR1CandidateParser.field.wide_exact.WideExact,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input=ok (some value) ∧
      parserCarrier value=out := by
  unfold viewFromBytes at accepted
  cases call : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input with
  | fail e => simp only [call,bind_tc_fail] at accepted;cases accepted
  | div => simp only [call,bind_tc_div] at accepted;cases accepted
  | ok value =>
    cases value with
    | none => simp only [call,bind_tc_ok,Option.map_none] at accepted;cases accepted
    | some value =>
      exact ⟨value,call,Option.some.inj (Result.ok.inj accepted)⟩

theorem physical (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    ∃ (input : Slice U8) (value : AspisR1CandidateParser.field.wide_exact.WideExact),
      bytesOf input.val=slice (bytesOf proof.val) 7495 32 ∧
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input=ok (some value) ∧
      parserCarrier value=view.inactive ∧ input.val.length=32 := by
  obtain ⟨input,rb,rr,root,range,parsed,rest⟩ := PAln_ViewCuts.selected proof semantic y1 view accepted
  obtain ⟨value,call,same⟩ := parser input view.inactive parsed
  have physical := PAln_Physical.range_bytes proof input 7495#usize 7527#usize range
  have length := (AspisR1.UnrolledWideParserRefinement.slice_success_canonical input value call).1
  refine ⟨input,value,?_,call,same,length⟩
  have a : (7495#usize).val=7495 := by scalar_tac
  have b : (7527#usize).val=7527 := by scalar_tac
  simpa only [a,b] using physical

#print axioms parser
#print axioms physical
end AspisR1.PAln_InactiveDecode
