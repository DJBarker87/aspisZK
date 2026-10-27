import RPz8_RawJ_DigestRead
import RPz7_S1SemanticCodeNewTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_InitRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem frame {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ frame, Read (observe (run (S1SemanticCode.newTranscript D hash pub root)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (decodeState root) := by
  let log := observe (run (S1SemanticCode.newTranscript D hash pub root)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.newTranscript D hash pub root)).1) frame →
      Read log frame := fun _ h => h
  change ∃ frame, Read log frame ∧ _
  unfold S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := right_read _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := right_read _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue len =>
    let parts := RawJ_DigestRead.initParts pub len root
    change erase (effects.digest D hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : r1_wire.SemanticTranscript H))) =
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail⟩ := AuS1_Trace.success_bind _ _ _ s3
    refine ⟨flatten parts,?_,RawJ_DigestRead.target pub len root⟩
    have member := left_read _ _ _ s3 _ (RawJ_DigestRead.digest D hash parts state digest)
    exact inc _ (sub1 _ (sub2 _ (sub3 _ member)))

#print axioms frame
end AspisR1.RawJ_InitRead
end
