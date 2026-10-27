import RPz8_RawK_Head
import RPz7_S1SemanticCodeNewTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_InitHead
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem first {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ len state,
      RawK_Head.head (S1SemanticCode.newTranscript D hash pub root) =
        some (flatten (RawJ_DigestRead.initParts pub len root),state) := by
  let log := RawK_Head.head (S1SemanticCode.newTranscript D hash pub root)
  have inc : ∀ entry, RawK_Head.head (S1SemanticCode.newTranscript D hash pub root) = some entry →
      log = some entry := fun _ h => h
  change ∃ len state, log = _
  unfold S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue len =>
    let parts := RawJ_DigestRead.initParts pub len root
    change erase (effects.digest D hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : r1_wire.SemanticTranscript H))) =
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ s3
    exact ⟨len,decodeState state,inc _ (sub1 _ (sub2 _ (sub3 _
      (RawK_Head.left _ _ _ s3 _ (RawK_Head.digest_head D hash parts state digest)))))⟩

theorem address_tag (pub : Slice U8) (len : U32) (root : Array U8 32#usize) :
    (flatten (RawJ_DigestRead.initParts pub len root)).head? = some 85 := by
  simp only [RawJ_DigestRead.initParts,flatten,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil]
  unfold r1_wire.DOMAIN
  rfl

#print axioms first
#print axioms address_tag
end AspisR1.RawK_InitHead
end
