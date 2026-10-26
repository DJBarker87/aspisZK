import F3P_ClaimsTrace
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsRows
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent

theorem source (external : External) (r : r1_wire.ValidatedRecord) (out : Claims)
    (h : decodeRows external r=ok (.Ok out)) :
    ∃ a b c,external.decode 29#usize r 0#usize=ok (.Ok a) ∧
      external.decode 29#usize r 29#usize=ok (.Ok b) ∧
      external.decode 29#usize r 58#usize=ok (.Ok c) ∧
      out=Array.make 3#usize [a,b,c] := by
  unfold decodeRows at h
  obtain ⟨r0,h0,h⟩ := F3P_ResultBind.success _ _ _ h
  cases r0 with
  | Err e => cases h
  | Ok a =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨r1,h1,h⟩ := F3P_ResultBind.success _ _ _ h
    cases r1 with
    | Err e => cases h
    | Ok b =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨r2,h2,h⟩ := F3P_ResultBind.success _ _ _ h
      cases r2 with
      | Err e => cases h
      | Ok c =>
        have same : Array.make 3#usize [a,b,c]=out := core.result.Result.Ok.inj (Result.ok.inj h)
        exact ⟨a,b,c,h0,h1,h2,same.symm⟩

#print axioms source
end AspisR1.F3P_ClaimsRows
