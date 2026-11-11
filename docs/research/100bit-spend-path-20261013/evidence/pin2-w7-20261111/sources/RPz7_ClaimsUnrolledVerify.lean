import RPz7_ClaimsUnrolledFinishAdapters
import RPz7_S1NativeBufferClaimTraceV1
/-! PIN2 W7 (2026-11-11): semantic_claims takes its facts from verify_roots; STATEMENT CHANGE: the public-init conjunct is now the PIN2 public_transcript on the PIN2W7_TranscriptCopy/toPIN2 copies (as verify_roots); other conjuncts unchanged.  -/
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
      AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (retainedDigest D))
        (AspisR1PublicPreparation.PreparationBinding.toPIN2 (FirstComposition.toRetainedPublic pub)) hash pre.c1_root=ok (.Ok (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.transcript initial)) ∧
      AspisR1PublicPreparation.r1_wire.begin (retainedDigest D) pre initial =
        ok (.Ok challenges, after) ∧
      AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children
        (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none =
          ok (.Ok (retainedSem sem)) ∧
      ClaimsUnrolledFinish.reference std pre = ok (.Ok (retainedSem sem).claims) := by
  have verified : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub bytes hash = ok (.Ok sem) := accepted
  obtain ⟨pre, initial, after, challenges, payload, root2, parsed, publicInit, begun, finished, _⟩ :=
    S1SemanticInstallation.verify_roots AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub bytes hash sem verified
  have claims := ClaimsUnrolledFinish.finish_claims std AspisS1ExtractedRoundChildren.children
    (AspisR1PublicPreparation.S1SemanticRootCopy.install B) (retainedDigest D)
    (FirstComposition.toRetainedPublic pub) pre after challenges none (retainedSem sem) finished
  exact ⟨pre, initial, after, challenges, parsed, publicInit, begun, finished, claims⟩

#print axioms semantic_claims
end AspisR1.ClaimsUnrolledSdk
end
