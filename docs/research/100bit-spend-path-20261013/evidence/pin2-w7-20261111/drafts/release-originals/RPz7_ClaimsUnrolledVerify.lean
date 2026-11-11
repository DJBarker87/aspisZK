import RPz7_ClaimsUnrolledFinishAdapters
import RPz7_S1NativeBufferClaimTraceV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation
open AspisR1CurrentCaller.S1SemanticCarrier

/-- The selected semantic call itself yields the parsed prefix, transcript,
begin and complete finish feeding Claims. No independent successful Claims or
finish call, chosen prefix or semantic output is assumed. This is the candidate
VALUE installation; native extraction/std/effects/adoption are not proved. -/
theorem semantic_claims
    (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none = ok (.Ok sem)) :
    ∃ (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (initial after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (challenges : AspisR1PublicPreparation.r1_wire.Challenges),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok pre) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root = ok (.Ok initial) ∧
      AspisR1PublicPreparation.r1_wire.begin (retainedDigest D) pre initial =
        ok (.Ok challenges, after) ∧
      AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children
        (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none =
          ok (.Ok (retainedSem sem)) ∧
      ClaimsUnrolledFinish.reference std pre = ok (.Ok (retainedSem sem).claims) := by
  have verified : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub bytes hash = ok (.Ok sem) := accepted
  have source := S1SemanticInstallation.verify_return AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub bytes hash sem verified
  obtain ⟨pre, initial, after, challenges, parsed, publicInit, begun, finished⟩ :=
    AspisR1PublicPreparation.S1SemanticVerify.verify_success _ _ _ _ _ none _ source
  have claims := ClaimsUnrolledFinish.finish_claims std AspisS1ExtractedRoundChildren.children
    (AspisR1PublicPreparation.S1SemanticRootCopy.install B) (retainedDigest D)
    (FirstComposition.toRetainedPublic pub) pre after challenges none (retainedSem sem) finished
  exact ⟨pre, initial, after, challenges, parsed, publicInit, begun, finished, claims⟩

#print axioms semantic_claims
end AspisR1.ClaimsUnrolledSdk
end
