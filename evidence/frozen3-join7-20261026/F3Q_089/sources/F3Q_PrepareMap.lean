import AuS1_Trace
import S1ClosedPreparationHashCodeV1
import S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PrepareMap
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared

theorem map_log {A B : Type} (c : Code A) (f : A → B) :
    (run (c >>= fun a=>pure (f a))).1=(run c).1 := by
  change (run (AspisR1PublicPreparation.PreparedHashCode.bind c _)).1=_
  rw [AuS1_Trace.run_bind]
  unfold AuS1_Trace.continueRun
  cases (run c).2 <;> simp only [run,List.append_nil]

theorem semantic {Hash : Type} (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : Hash) :
    (run (S1SemanticCodeInstallation.code R B D pub bytes hash)).1=
    (run (AspisR1PublicPreparation.S1SemanticCode.verify
      (AspisR1PublicPreparation.S1SemanticCode.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
      (retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes hash none)).1 := by
  unfold S1SemanticCodeInstallation.code
  exact map_log _ _

theorem original {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (sem : r1_semantic.Verified Hash) (v : verifier.View) (hash : Hash)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (run (closedPreparationCode D sem v hash scratch)).1=
    (run (AspisR1PublicPreparation.PreparedSourceEffects.prepare
      (preparationEffects closedHashBoundaries closedHashQueries) (retainedDigest D) (retainedSem sem)
      (retainedView v) hash (AspisR1ClaimPreparedBridge.mapArray retainedE scratch))).1 := by
  unfold closedPreparationCode
  exact map_log _ _

#print axioms map_log
#print axioms semantic
#print axioms original
end AspisR1.F3Q_PrepareMap
end
