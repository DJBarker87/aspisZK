import RPu_FJa_ClaimsDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ClaimsRows
open Aeneas Aeneas.Std Result
open ClaimsUnrolledFinish
/-- All three rows are decoded from the SAME actual record and offsets0/29/58. -/
theorem value (std : StdCalls) (r : AspisR1ClaimsUnrolledParent.Record)
    (out : AspisR1ClaimsUnrolledParent.Claims)
    (run : AspisR1ClaimsUnrolledParent.decodeRows (external std) r=ok (.Ok out)) :
    ∀ row∈out.val,∀ q∈row.val,FIp_SemanticValues.Canon (toMainQM q) := by
  unfold AspisR1ClaimsUnrolledParent.decodeRows at run
  obtain ⟨s0,h0,run⟩ := FIv_Map.bind_success _ _ _ run
  cases s0 with
  | Err e => cases run
  | Ok row0 =>
    obtain ⟨s1,h1,run⟩ := FIv_Map.bind_success _ _ _ run
    cases s1 with
    | Err e => cases run
    | Ok row1 =>
      obtain ⟨s2,h2,run⟩ := FIv_Map.bind_success _ _ _ run
      cases s2 with
      | Err e => cases run
      | Ok row2 =>
        have same : (⟨[row0,row1,row2],by simp⟩ : AspisR1ClaimsUnrolledParent.Claims)=out :=
          core.result.Result.Ok.inj (Result.ok.inj run)
        subst out
        intro row member q hq
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl
        · exact FJa_ClaimsDecode.value 29#usize r 0#usize row h0 q hq
        · exact FJa_ClaimsDecode.value 29#usize r 29#usize row h1 q hq
        · exact FJa_ClaimsDecode.value 29#usize r 58#usize row h2 q hq
#print axioms value
end AspisR1.FJa_ClaimsRows
end
