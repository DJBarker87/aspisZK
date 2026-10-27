import RPz7_F3N_PreparedClaimSource
set_option autoImplicit false
namespace AspisR1.F3P_SemanticDecode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem cells {H : Type} (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (pre : r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify R B D pub bytes hash=ok (.Ok sem)) :
    ∃ r25 r26,
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      R.decode 29#usize r25 87#usize=ok (.Ok (retainedSem sem).extra) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      R.decode 29#usize r26 0#usize=ok (.Ok (retainedSem sem).before_z1) ∧
      (S1SemanticRootCopy.install B).claims pre=ok (.Ok (retainedSem sem).claims) := by
  obtain ⟨actual,initial,after,challenges,payload,root,called,publicInit,begin,finish,rest⟩ :=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots R B D pub bytes hash sem success
  have same := core.result.Result.Ok.inj (Result.ok.inj (called.symm.trans parsed))
  subst actual
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,rounds,challenge,state,transcript,claims,
    read25,extra,circle0,read26,before,circle1,points⟩ :=
    S1SemanticFinishBounds.finish_success R (S1SemanticRootCopy.install B) (retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre after challenges none
      (retainedSem sem) finish
  exact ⟨r25,r26,read25,extra,read26,before,claims⟩

#print axioms cells
end AspisR1.F3P_SemanticDecode
