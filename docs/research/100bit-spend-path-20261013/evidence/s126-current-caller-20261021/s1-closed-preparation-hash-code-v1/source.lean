import S1PreparedCompleteHashErasureV1
import S1ClosedPreparationInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open OriginalSerializerInstallation

private abbrev PBoundaries := AspisR1PublicPreparation.PreparedScratchModel.Boundaries

def closedHashBoundaries : PBoundaries :=
  concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed)

def closedHashQueries : AspisR1PublicPreparation.QueriesModel.Boundaries :=
  Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed

theorem closedHashBoundaries_queries :
    AspisR1PublicPreparation.PreparedHashCode.withQueries closedHashBoundaries closedHashQueries=
      closedHashBoundaries := by
  rfl

/-- Full current caller carriers and its actual installed child procedures.
No free sampling/query record and no independent successful child call. -/
def closedPreparationCode {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) := do
  let (r,g) ← AspisR1PublicPreparation.PreparedSourceEffects.prepare
    (AspisR1PublicPreparation.PreparedHashCode.preparationEffects closedHashBoundaries closedHashQueries)
    (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
    (InstalledPreparation.retainedView v) hash (mapArray InstalledPreparation.retainedE scratch)
  pure ((match r with
    | .Ok x => .Ok (InstalledPreparation.currentPrepared x)
    | .Err e => .Err (InstalledPreparation.currentError e)),
    mapArray InstalledPreparation.currentE g)

/-- Exact current originalNew operation, on all outcomes. This supplies a
source-shaped trace representation; native digest interpretation and the
non-hash children' purity/source installation remain separate obligations. -/
theorem closedPreparationCode_erasure {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    AspisR1PublicPreparation.PreparedHashCode.erase (closedPreparationCode D sem v hash scratch)=
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem v hash scratch := by
  rw [originalNew_eq_transport]
  unfold closedPreparationCode
  rw [AspisR1PublicPreparation.PreparedHashCode.erase_bind,
    AspisR1PublicPreparation.PreparedHashCode.preparation_erasure,closedHashBoundaries_queries,
    AspisR1PublicPreparation.OriginalPreparedNative.eq_prepare]
  rfl

theorem closedPreparationCode_run_value {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (AspisR1PublicPreparation.PreparedHashCode.run (closedPreparationCode D sem v hash scratch)).2=
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem v hash scratch := by
  rw [AspisR1PublicPreparation.PreparedHashCode.run_value,closedPreparationCode_erasure]

#print axioms closedHashBoundaries_queries
#print axioms closedPreparationCode_erasure
#print axioms closedPreparationCode_run_value
end AspisR1CurrentCaller.BorrowedClaimPrepared
