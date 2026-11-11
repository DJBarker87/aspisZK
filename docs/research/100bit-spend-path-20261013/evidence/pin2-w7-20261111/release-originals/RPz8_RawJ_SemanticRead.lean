import RPz8_RawJ_VerifyRead
import RPz7_S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SemanticRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix
open AspisR1CurrentCaller

theorem frame (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (out : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : erase (S1SemanticCodeInstallation.code R B D pub input hash) = ok (.Ok out)) :
    ∃ p, PrefixAdapter.parseAccepted input = ok (.Ok p) ∧
      ∃ frame, Read (observe (run (S1SemanticCodeInstallation.code R B D pub input hash)).1) frame ∧
        BinRawByteCollisionTargets.pred 2 frame = some (decodeState p.c1_root) := by
  unfold S1SemanticCodeInstallation.code at success ⊢
  obtain ⟨result,call,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  cases result with
  | Err e => rw [erase_pure] at tail; cases tail
  | Ok sem =>
    obtain ⟨p,parsed,frame,read,target⟩ := RawJ_VerifyRead.frame _ _ _ _ _ _ sem call
    exact ⟨p,parsed,frame,left_read _ _ _ success frame read,target⟩

#print axioms frame
end AspisR1.RawJ_SemanticRead
end
