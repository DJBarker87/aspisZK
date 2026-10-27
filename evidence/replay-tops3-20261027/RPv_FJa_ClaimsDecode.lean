import RPz7_ClaimsUnrolledFinish
import RPu_FIq_S_RawActualDecodeKMainAdapter
import RPt_FIp_SemanticValues
import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ClaimsDecode
open Aeneas Aeneas.Std Result
open ClaimsUnrolledFinish
/-- Canonicality of actual sourceDecode outputs follows from the complete
installed decodeMain reader, with no per-cell canonicality assumption. -/
theorem value (n : Usize) (r : AspisR1ClaimsUnrolledParent.Record) (offset : Usize)
    (out : Array ParentQM n)
    (run : sourceDecode n r offset=ok (.Ok out)) :
    ∀ q∈out.val,FIp_SemanticValues.Canon (toMainQM q) := by
  unfold sourceDecode at run
  cases hd : AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord r) offset with
  | fail e => rw [hd] at run;cases run
  | div => rw [hd] at run;cases run
  | ok result =>
    rw [hd] at run
    cases result with
    | Err e => cases run
    | Ok a =>
      have same : fromMainArray a=out := core.result.Result.Ok.inj (Result.ok.inj run)
      subst out
      intro q hq
      obtain ⟨original,member,rfl⟩ := List.mem_map.mp hq
      have h := AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain_success_members_canonical n (toMainRecord r) offset a hd original member
      exact h
#print axioms value
end AspisR1.FJa_ClaimsDecode
end
