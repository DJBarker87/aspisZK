import JGi_ClaimArrays
import ClaimsUnrolledFinishAdapters
import NP6_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPs_ClaimsDomain
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish

private theorem step_success {A : Type}
    (m : Result (core.result.Result A ParentError))
    (k : A → Result AspisR1ClaimsUnrolledParent.Status) (out : MainClaims)
    (success : toMainStatus (do
      let r ← m
      match r with
      | .Err e => ok (.Err e)
      | .Ok a => k a)=ok (.Ok out)) :
    ∃ a,m=ok (.Ok a) ∧ toMainStatus (k a)=ok (.Ok out) := by
  cases m with
  | fail e => cases success
  | div => cases success
  | ok r =>
    cases r with
    | Err e => cases success
    | Ok a => exact ⟨a,rfl,success⟩

theorem decoded (r : AspisR1ClaimsUnrolledParent.Record) (off : Usize)
    (row : Array ParentQM 29#usize)
    (call : sourceDecode 29#usize r off=ok (.Ok row)) :
    JGi_ClaimArrays.RowCanonical (toMainArray row) := by
  have port := congrArg toMainDecoded call
  rw [decode_exact] at port
  exact JGi_ClaimArrays.decoded (toMainRecord r) off (toMainArray row) port

theorem claims (pre : MainPrefix) (out : MainClaims)
    (success : ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out)) :
    ∀ row ∈ out.val, JGi_ClaimArrays.RowCanonical row := by
  rw [claims_value] at success
  unfold reference at success
  rw [NP6_ClaimsModel.reference_normalized] at success
  unfold NP6_ClaimsModel.normalized at success
  obtain ⟨r,record,success⟩ := step_success _ _ _ success
  change toMainStatus (AspisR1ClaimsUnrolledParent.decodeRows
    (external (NP6_StdModel.calls (.Ok ()))) r)=ok (.Ok out) at success
  unfold AspisR1ClaimsUnrolledParent.decodeRows at success
  obtain ⟨a,da,success⟩ := step_success _ _ _ success
  obtain ⟨b,db,success⟩ := step_success _ _ _ success
  obtain ⟨c,dc,success⟩ := step_success _ _ _ success
  have same := core.result.Result.Ok.inj (Result.ok.inj success)
  subst out
  intro row member
  change row ∈ [toMainArray a,toMainArray b,toMainArray c] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact decoded r 0#usize a da
  · exact decoded r 29#usize b db
  · exact decoded r 58#usize c dc

#print axioms step_success
#print axioms decoded
#print axioms claims
end AspisR1.LPs_ClaimsDomain
end
