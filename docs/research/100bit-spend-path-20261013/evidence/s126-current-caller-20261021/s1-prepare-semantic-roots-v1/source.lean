import S1SemanticInstallationV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open S1SemanticInstallation

/-- SAME complete preparation, now with the full semantic verifier body
installed rather than a free op9 return. Both returned roots, the real parsed
semantic prefix and row-2 copy are derived from that ONE accepted execution.
Semantic arithmetic/circle/std/runtime leaf installation remains explicit. -/
theorem prepare_semantic_roots (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (closedInstall (S1SemanticInstallation.install ops R B))
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    prepared.variant=.S2 ∧
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H)
      (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (initial after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
      (payload : Slice U8) (root2 : Array U8 32#usize),
      sourceView proof semantic y1=ok (.Ok view) ∧
      S1SemanticInstallation.verify R B D pub view.semantic hash=ok (.Ok sem) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted view.semantic=ok (.Ok pre) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok initial) ∧
      AspisR1PublicPreparation.r1_wire.begin (retainedDigest D) pre initial=ok (.Ok challenges,after) ∧
      AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)
        (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none=ok (.Ok (retainedSem sem)) ∧
      AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Ok root2) ∧
      root2.val=payload.val ∧ prepared.roots=Array.make 2#usize [pre.c1_root,root2] := by
  obtain ⟨variant,semantic,y1,view,sem,hview,hsem,hnew,roots,alpha,coordinates⟩ :=
    closed_prepare_provenance (S1SemanticInstallation.install ops R B) D pub proof hash prepared input scratch success
  change S1SemanticInstallation.verify R B D pub view.semantic hash=ok (.Ok sem) at hsem
  obtain ⟨pre,initial,after,challenges,payload,root2,parsed,publicInit,begin,finish,hpayload,hcopy,hbytes,hroots⟩ :=
    S1SemanticInstallation.verify_roots R B D pub view.semantic hash sem hsem
  exact ⟨variant,semantic,y1,view,sem,pre,initial,after,challenges,payload,root2,
    hview,hsem,parsed,publicInit,begin,finish,hpayload,hcopy,hbytes,roots.trans hroots⟩

#print axioms prepare_semantic_roots
end AspisR1CurrentCaller.BorrowedClaimPrepared
