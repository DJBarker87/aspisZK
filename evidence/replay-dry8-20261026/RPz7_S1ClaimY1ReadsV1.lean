import RPz7_S1ClosedPrepareRangesV1
import RPz7_S1WideViewY1V1
set_option autoImplicit false
namespace AspisR1ClaimPreparedBridge
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim Concrete

/-- Exact point-5 coverage: every source column appears, not merely every
member of a possibly short read list. Full parser outputs are retained. -/
theorem original_payload_y1_fields {H : Type}
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive gamma kappa out : E) (g : Array E 29#usize)
    (meaning : OriginalPayloadClaimMeaning sem y1 inactive gamma kappa out g) :
    ∀ l : Usize, l.val<29 → ∃ parsed : E,
      ClaimParser.field y1 l=ok parsed ∧ Canonical parsed := by
  obtain ⟨final,zero,points,canonicalOut,decodedOut⟩ := meaning
  obtain ⟨i,value,hi,xs,increment,cell,length,order,reads,decoded⟩ := points 5#usize (by decide)
  intro l bound
  have idx : l.val<xs.length := by omega
  let selected := xs[l.val]'idx
  have member : selected ∈ xs := List.getElem_mem idx
  have column : selected.1=l := UScalar.eq_of_val_eq (order l.val idx)
  obtain ⟨parsed,read,canonical,scalar⟩ := (reads selected member).1.2.2.2 rfl
  rw [column] at read
  exact ⟨parsed,read,canonical⟩

#print axioms original_payload_y1_fields
end AspisR1ClaimPreparedBridge

namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open OriginalSerializerInstallation

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- Same View and original new/scratch call. Inactive canonicality and all
29 field successes follow from these source calls; no per-field witness is
supplied. ACCEPTED-ONLY; native abort/Std correspondence remains separate. -/
theorem original_new_y1_fields {H : Type} (D : aspis_core.digest.Digest32 H)
    (proof semantic bytes : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H)
    (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (viewCall : sourceView proof semantic bytes=ok (.Ok view))
    (newCall : originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
      D sem view hash input=ok (.Ok prepared,scratch)) :
    ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
      AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧ Canonical parsed := by
  unfold sourceView at viewCall
  obtain ⟨reply,sourceViewCall,viewCall⟩ := bind_success _ _ _ viewCall
  cases reply with
  | Err error => cases viewCall
  | Ok old =>
    have same : selectedView old=view := core.result.Result.Ok.inj (Result.ok.inj viewCall)
    subst view
    rw [originalNew_eq_transport] at newCall
    obtain ⟨pair,backend,newCall⟩ := bind_success _ _ _ newCall
    rcases pair with ⟨reply,g⟩
    cases reply with
    | Err error => cases newCall
    | Ok source =>
      rw [retained_selected_view] at backend
      have inactive := AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic bytes old sourceViewCall
      obtain ⟨canonical,alpha,claim,powers⟩ := prepared_installed_meaning
        (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        (retainedDigest D) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView old)
        hash source g (mapArray retainedE input) inactive backend
      exact original_payload_y1_fields _ _ _ _ _ _ _ claim

#print axioms original_new_y1_fields
end AspisR1CurrentCaller.BorrowedClaimPrepared
