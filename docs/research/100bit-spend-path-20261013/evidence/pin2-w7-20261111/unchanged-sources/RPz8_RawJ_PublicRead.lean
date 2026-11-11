import RPz8_RawJ_InitRead
import RPz7_S1SemanticCodePublicTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_PublicRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem frame {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.publicTranscript D pub hash root) = ok (.Ok out)) :
    ∃ frame, Read (observe (run (S1SemanticCode.publicTranscript D pub hash root)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (decodeState root) := by
  let log := observe (run (S1SemanticCode.publicTranscript D pub hash root)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.publicTranscript D pub hash root)).1) frame →
      Read log frame := fun _ h => h
  change ∃ frame, Read log frame ∧ _
  unfold S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := right_read _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := right_read _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue value =>
    obtain ⟨frame,read,target⟩ := RawJ_InitRead.frame D hash value.deref root out s3
    exact ⟨frame,inc _ (sub1 _ (sub2 _ (sub3 _ read))),target⟩

#print axioms frame
end AspisR1.RawJ_PublicRead
end
