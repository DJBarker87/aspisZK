import RPu_FIq_S_RawActualAnnotatedChallengeSequence
import RPu_FIq_Install
import RPz7_F3P_SemanticDecode
import RPz7_PSem_SourceCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIq_SemanticSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open RawActualAnnotatedPolynomialRun

theorem children_same : AspisS1ExtractedRoundChildren.children=
    RawActualSemanticRoundCanonicality.actualRoundBoundaries := rfl

/-- The accepted semantic call supplies the SAME row14 decode and all ten
actual source polynomial recurrence steps. No separate successful rounds call
or independent coefficient/challenge sequence is a hypothesis. -/
theorem verified {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify
      AspisS1ExtractedRoundChildren.children B D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
      (running : aspis_core.field.QM31) (record : r1_wire.ValidatedRecord)
      (decoded : Array aspis_core.field.QM31 1#usize) (initial : aspis_core.field.QM31)
      (entries : List (RoundEvidence (retainedDigest D) pre)),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      RoundModel.rounds AspisS1ExtractedRoundChildren.children (retainedDigest D) pre before=
        ok (.Ok (running,(retainedSem sem).alpha,after)) ∧
      r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok record) ∧
      AspisS1ExtractedRoundChildren.decodeMain 1#usize record 0#usize=ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize=ok initial ∧
      AnnotatedRun (retainedDigest D) pre SemanticRoundsCheckedTrace.schedule
        (initial,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before)
        (running,(retainedSem sem).alpha,after) entries ∧
      entries.map RoundEvidence.q=(retainedSem sem).alpha.val ∧
      RawGenericPolynomialSumcheckChain.Chain (DecodeMain initial) (DecodeMain running)
        (entries.map (pairOf (retainedDigest D) pre)) := by
  obtain ⟨pre,initialTranscript,before,cs,payload,root,parsed,publicInit,begin,finish,rest⟩ :=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots
      AspisS1ExtractedRoundChildren.children B D pub bytes hash sem success
  obtain ⟨running,after,r25,r26,z0,t26,z1,t27,rounds,tail⟩ :=
    S1SemanticFinishBounds.finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install B) (retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre before cs none
      (retainedSem sem) finish
  have actual : RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries
      (retainedDigest D) pre before=ok (.Ok (running,(retainedSem sem).alpha,after)) := by
    rw [← children_same]
    exact rounds
  obtain ⟨record,decoded,initial,entries,read,decode,index,annotated,values⟩ :=
    RawActualAnnotatedChallengeSequence.rounds_success_annotated_challenges_eq_alpha
      (retainedDigest D) pre before after running (retainedSem sem).alpha actual
  have chain := annotatedRun_to_chain (retainedDigest D) pre _ _ _ entries annotated
  exact ⟨pre,before,after,running,record,decoded,initial,entries,parsed,rounds,
    read,decode,index,annotated,values,chain⟩

#print axioms children_same
#print axioms verified
end AspisR1.FIq_SemanticSource
end
