import RPz7_F3U_VerifyHead
import RPz7_S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SemanticHead
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem first (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (out : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : erase (S1SemanticCodeInstallation.code R B D pub input hash)=ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (root state : State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic pub)=ok (.Ok encoded) ∧
      RawK_Head.head (S1SemanticCodeInstallation.code R B D pub input hash)=
        some (AspisR1.PublicInitFrame.frame (SourceDigestAddresses.rawBytes encoded.deref) root,state) := by
  unfold S1SemanticCodeInstallation.code at success ⊢
  obtain ⟨result,call,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  cases result with
  | Err e => rw [erase_pure] at tail; cases tail
  | Ok sem =>
    obtain ⟨encoded,root,state,serialized,read⟩ := F3U_VerifyHead.first _ _ _ _ _ _ sem call
    exact ⟨encoded,root,state,serialized,RawK_Head.left _ _ _ success _ read⟩

#print axioms first
end AspisR1.F3U_SemanticHead
end
