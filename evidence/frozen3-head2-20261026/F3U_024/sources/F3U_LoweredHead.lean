import RawK_CodeHead
import F3U_PrepareHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_LoweredHead
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisR1CurrentCaller
theorem first {Hash : Type} (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (source : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : erase (SdkC_Source.dictionary hashv) () (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) = ok (.Ok p,scratch)) :
    ∃ (encoded : alloc.vec.Vec U8) (root state : AspisV8R19.SourceDuplexStep.State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic pub)=ok (.Ok encoded) ∧
      RawK_CodeHead.head hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code ops B std D pub proof hash input))=
        some (AspisR1.PublicInitFrame.frame (AspisR1PublicPreparation.SourceDigestAddresses.rawBytes encoded.deref) root,state) := by
  have association := GExp_PrepareAssociation.prepare ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash input hashv source
  have logs := GExp_LowerTrace.log hashv (SdkD_PrepareSource.code ops B std D pub proof hash input) association
  have erased := (SdkD_PrepareLower.erasure hashv
    (SdkD_PrepareSource.code ops B std D pub proof hash input) association).symm.trans success
  change AspisR1PublicPreparation.PreparedHashCode.erase
    (S1PrepareCode.prepare ops AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub proof hash input) = _ at erased
  obtain ⟨encoded,root,state,serialized,h⟩ := F3U_PrepareHead.reached _ _ _ D pub proof hash p input scratch erased
  refine ⟨encoded,root,state,serialized,?_⟩
  unfold RawK_CodeHead.head
  have ht := congrArg List.head? logs
  unfold SdkD_PrepareSource.code at ht ⊢
  exact ht.trans h

#print axioms first
end AspisR1.F3U_LoweredHead
end
