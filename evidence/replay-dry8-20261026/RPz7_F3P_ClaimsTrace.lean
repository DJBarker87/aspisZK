import RPz7_F3P_ResultBind
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsTrace
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent

theorem source (external : External) (pre : r1_wire.Prefix) (out : Claims)
    (h : claimsReference external pre=ok (.Ok out)) :
    ∃ r,external.validated pre 25#u8=ok (.Ok r) ∧ decodeRows external r=ok (.Ok out) := by
  unfold claimsReference at h
  obtain ⟨result,read,h⟩ := F3P_ResultBind.success _ _ _ h
  cases result with
  | Err e => cases h
  | Ok r =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨q,zero,h⟩ := F3P_ResultBind.success _ _ _ h
    obtain ⟨filled,allocated,h⟩ := F3P_ResultBind.success _ _ _ h
    obtain ⟨mapped,mapping,h⟩ := F3P_ResultBind.success _ _ _ h
    cases mapped with
    | Err e => cases h
    | Ok buffer =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨slice,boxed,h⟩ := F3P_ResultBind.success _ _ _ h
      obtain ⟨array,converted,h⟩ := F3P_ResultBind.success _ _ _ h
      obtain ⟨mappedArray,mapped,h⟩ := F3P_ResultBind.success _ _ _ h
      cases mappedArray with
      | Err e => cases h
      | Ok a => exact ⟨r,read,h⟩

#print axioms source
end AspisR1.F3P_ClaimsTrace
