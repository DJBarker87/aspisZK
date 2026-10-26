import F3P_ClaimsRows
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsMain
open Aeneas Aeneas.Std Result

theorem reference (std : ClaimsUnrolledFinish.StdCalls) (pre : ClaimsUnrolledFinish.MainPrefix)
    (out : ClaimsUnrolledFinish.MainClaims)
    (success : ClaimsUnrolledFinish.reference std pre=ok (.Ok out)) :
    ∃ (r : AspisR1ClaimsUnrolledParent.r1_wire.ValidatedRecord)
      (a b c : AspisR1ClaimsUnrolledParent.Row),
      ClaimsUnrolledFinish.sourceRecord (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8=ok (.Ok r) ∧
      ClaimsUnrolledFinish.sourceDecode 29#usize r 0#usize=ok (.Ok a) ∧
      ClaimsUnrolledFinish.sourceDecode 29#usize r 29#usize=ok (.Ok b) ∧
      ClaimsUnrolledFinish.sourceDecode 29#usize r 58#usize=ok (.Ok c) ∧
      out=Array.make 3#usize [ClaimsUnrolledFinish.toMainArray a,
        ClaimsUnrolledFinish.toMainArray b,ClaimsUnrolledFinish.toMainArray c] := by
  unfold ClaimsUnrolledFinish.reference at success
  cases h : AspisR1ClaimsUnrolledParent.claimsReference (ClaimsUnrolledFinish.external std)
      (ClaimsUnrolledFinish.fromMainPrefix pre) with
  | fail e => simp only [h,ClaimsUnrolledFinish.toMainStatus] at success;cases success
  | div => simp only [h,ClaimsUnrolledFinish.toMainStatus] at success;cases success
  | ok result =>
    cases result with
    | Err e => simp only [h,ClaimsUnrolledFinish.toMainStatus] at success;cases success
    | Ok original =>
      simp only [h,ClaimsUnrolledFinish.toMainStatus] at success
      obtain ⟨r,read,rows⟩ := F3P_ClaimsTrace.source _ _ original h
      obtain ⟨a,b,c,d0,d1,d2,same⟩ := F3P_ClaimsRows.source _ r original rows
      refine ⟨r,a,b,c,read,d0,d1,d2,?_⟩
      have outEq := (core.result.Result.Ok.inj (Result.ok.inj success)).symm
      rw [outEq,same]
      rfl

#print axioms reference
end AspisR1.F3P_ClaimsMain
