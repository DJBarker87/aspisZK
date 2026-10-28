import NBN_StatementEncoderSummary
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderObservation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open NBN_StatementEncoderSummary

theorem faithful : Function.Injective observe := by
  intro x y h
  cases x with
  | fail e => cases y <;> simp_all [observe]
  | div => cases y <;> simp_all [observe]
  | ok a =>
    cases y with
    | fail e => simp_all [observe]
    | div => simp_all [observe]
    | ok b =>
      cases a <;> cases b <;> simp_all [observe,Subtype.ext_iff]

/-- List observation preserves the exact successful output width. -/
theorem width (r : Result (core.result.Result (Array U8 1880#usize) NBN_StatementResult.Error))
    (bs : List U8) (h : observe r = ok (.Ok bs)) : bs.length = 1880 := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok a =>
    cases a with
    | Err e => cases h
    | Ok b =>
      have same : b.val = bs := by simpa only [observe,bind_tc_ok,Result.ok.injEq,core.result.Result.Ok.injEq] using h
      rw [← same]
      exact b.property

#print axioms faithful
#print axioms width
end NBN_EncoderObservation
