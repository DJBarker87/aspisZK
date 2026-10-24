import S1TopPowersV1
import S1ClosedPrepareRangesV1
set_option autoImplicit false
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisS1TopPowers
open AspisR1ClaimPreparedBridge AspisR1CurrentCaller.InstalledPreparation

/-- At the complete top op7 boundary, gamma and kappa ranges follow from
its SAME successful preparation. No separate canonical-input premise. -/
theorem prepare_gamma_kappa_canonical (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : prepare ops D pub proof hash none input=ok (.Ok prepared,scratch)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical (claimE prepared.gamma) ∧
    AspisR1CurrentPreparedClaim.Concrete.Canonical (claimE prepared.kappa) := by
  obtain ⟨current,g,source,same,scratchEq⟩ := prepare_return ops D pub proof hash input scratch prepared success
  obtain ⟨original,originalG,preparedEq,gEq,canonical,alpha,powers⟩ :=
    AspisR1CurrentCaller.BorrowedClaimPrepared.closed_prepare_ranges ops (currentDigest D)
      _ proof hash current (mapArray fromE input) g source
  rw [same,preparedEq]
  exact canonical

/-- All 29 cells of the SAME returned scratch are canonical gamma powers.
No new preparation, scratch equality or successful powers call is assumed. -/
theorem prepare_scratch_exact (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : prepare ops D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
      Array.index_usize (mapArray claimE scratch) i=ok value ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical value ∧
      AspisR1CurrentPreparedClaim.Concrete.decode value=
        AspisR1CurrentPreparedClaim.Concrete.decode (claimE prepared.gamma)^i.val := by
  obtain ⟨current,g,source,same,scratchEq⟩ := prepare_return ops D pub proof hash input scratch prepared success
  obtain ⟨original,originalG,preparedEq,gEq,canonical,alpha,powers⟩ :=
    AspisR1CurrentCaller.BorrowedClaimPrepared.closed_prepare_ranges ops (currentDigest D)
      _ proof hash current (mapArray fromE input) g source
  rw [scratchEq,gEq,same,preparedEq]
  have mapped : mapArray claimE (mapArray toE (mapArray currentE originalG))=
      mapArray toClaimE originalG := by
    apply Subtype.ext
    simp only [mapArray,List.map_map]
    rfl
  rw [mapped]
  exact powers

#print axioms prepare_gamma_kappa_canonical
#print axioms prepare_scratch_exact
end AspisS1TopPrepareSource
