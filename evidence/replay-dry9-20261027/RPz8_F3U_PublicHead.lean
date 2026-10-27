import RPz8_F3U_InitAddress
import RPz7_S1SemanticCodePublicTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_PublicHead
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem first {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.publicTranscript D pub hash root)=ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (state : State),
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded) ∧
      RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root)=
        some (AspisR1.PublicInitFrame.frame (rawBytes encoded.deref) (decodeState root),state) := by
  let log := RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root)
  have inc : ∀ entry, RawK_Head.head (S1SemanticCode.publicTranscript D pub hash root)=some entry →
      log=some entry := fun _ h=>h
  change ∃ encoded state, _ ∧ log=_
  unfold S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue encoded =>
    have serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded) := by
      rw [erase_lift] at hr hr1 hcf
      cases r1 with
      | Err e => cases hcf
      | Ok n =>
        have same : n=encoded := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj hcf)
        subst n
        cases r with
        | Err e =>
          cases he : r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once D () e <;>
            simp [core.result.Result.map_err,he] at hr1
        | Ok n =>
          simp only [core.result.Result.map_err] at hr1
          have same : n=encoded := core.result.Result.Ok.inj (Result.ok.inj hr1)
          rw [same] at hr
          exact hr
    obtain ⟨state,head⟩ := F3U_InitAddress.head D hash encoded.deref root out s3
    exact ⟨encoded,state,serialized,inc _ (sub1 _ (sub2 _ (sub3 _ head)))⟩

#print axioms first
end AspisR1.F3U_PublicHead
end
