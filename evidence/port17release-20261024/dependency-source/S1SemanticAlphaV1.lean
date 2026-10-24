import S1SemanticInstallationV1
import S1SemanticFinishBoundsV1
import SemanticRoundAlphaSelectedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.S1SemanticInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge

def CanonicalQ (q : aspis_core.field.QM31) : Prop :=
  (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
  (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)

/-- The SAME source semantic verification supplies every alpha word bound.
No alpha range, successful round call or chosen challenge array is assumed. -/
theorem verify_alpha (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R B D pub bytes hash=ok (.Ok sem)) :
    ∀ i : Fin 10, CanonicalQ (sem.alpha.val[i.val]'(by simpa [sem.alpha.property] using i.isLt)) := by
  have source := verify_return R B D pub bytes hash sem success
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    AspisR1PublicPreparation.S1SemanticVerify.verify_success _ _ _ _ _ none _ source
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,rest⟩ :=
    AspisR1PublicPreparation.S1SemanticFinishBounds.finish_success R
      (AspisR1PublicPreparation.S1SemanticRootCopy.install B) (retainedDigest D)
      (FirstComposition.toRetainedPublic pub) pre after challenges none (retainedSem sem) finish
  have canonical := AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
    R (retainedDigest D) pre after t25 running (retainedSem sem).alpha rounds
  intro i
  have cell := canonical i
  simp only [retainedSem,mapArray,List.getElem_map] at cell
  exact cell

#print axioms verify_alpha
end AspisR1CurrentCaller.S1SemanticInstallation
