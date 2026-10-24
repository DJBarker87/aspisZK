import S1SemanticCircleV1
import S1PrepareSemanticRootsV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1SemanticInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge

/-- Both coordinates of every returned source semantic point are canonical
on this same verification return; no independently chosen sampling run. -/
theorem verify_z (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R (AspisR1PublicPreparation.S1SemanticCircle.install B)
      D pub bytes hash=ok (.Ok sem)) :
    ∀ p ∈ sem.z.val, CanonicalQ p.x ∧ CanonicalQ p.y := by
  have source := verify_return R _ D pub bytes hash sem success
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    AspisR1PublicPreparation.S1SemanticVerify.verify_success _ _ _ _ _ none _ source
  have canonical := AspisR1PublicPreparation.S1SemanticCircle.finish_z_canonical
    R B (retainedDigest D) (FirstComposition.toRetainedPublic pub)
    pre after challenges (retainedSem sem) finish
  intro p hp
  have member : retainedPoint p ∈ (retainedSem sem).z.val := by
    change retainedPoint p ∈ sem.z.val.map retainedPoint
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact canonical (retainedPoint p) member

/-- The same complete preparation, including its original returned scratch,
derives the coordinate bounds of its own Prepared.z. Other child associations
remain explicit and this is not a native SDK closure claim. -/
theorem prepare_z (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare
      (BorrowedClaimPrepared.closedInstall
        (install ops R (AspisR1PublicPreparation.S1SemanticCircle.install B)))
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∀ p ∈ prepared.z.val, CanonicalQ p.x ∧ CanonicalQ p.y := by
  obtain ⟨variant,semantic,y1,view,sem,hview,hsem,hnew,roots,alpha,coordinates⟩ :=
    BorrowedClaimPrepared.closed_prepare_provenance
      (install ops R (AspisR1PublicPreparation.S1SemanticCircle.install B))
      D pub proof hash prepared input scratch success
  change verify R (AspisR1PublicPreparation.S1SemanticCircle.install B)
    D pub view.semantic hash=ok (.Ok sem) at hsem
  rw [coordinates]
  exact verify_z R B D pub view.semantic hash sem hsem

#print axioms verify_z
#print axioms prepare_z
end AspisR1CurrentCaller.S1SemanticInstallation
