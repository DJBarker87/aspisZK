import RPz8_RawK_VerifyHead
import RPz7_S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_SemanticHead
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller

theorem first (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (out : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : erase (S1SemanticCodeInstallation.code R B D pub input hash) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (S1SemanticCodeInstallation.code R B D pub input hash) = some entry ∧
      entry.1.head? = some 85 := by
  unfold S1SemanticCodeInstallation.code at success ⊢
  obtain ⟨result,call,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  cases result with
  | Err e => rw [erase_pure] at tail; cases tail
  | Ok sem =>
    obtain ⟨entry,read,tag⟩ := RawK_VerifyHead.first _ _ _ _ _ _ sem call
    exact ⟨entry,RawK_Head.left _ _ _ success entry read,tag⟩

#print axioms first
end AspisR1.RawK_SemanticHead
end
