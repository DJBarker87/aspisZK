import RawK_InitHead
import S1SemanticCodePublicTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_PublicHead
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem first {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.publicTranscript D pub hash root) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root)
  have inc : ∀ entry, RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
  unfold S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue value =>
    obtain ⟨len,state,h⟩ := RawK_InitHead.first D hash value.deref root out s3
    exact ⟨_,inc _ (sub1 _ (sub2 _ (sub3 _ h))),RawK_InitHead.address_tag _ _ _⟩

#print axioms first
end AspisR1.RawK_PublicHead
end
