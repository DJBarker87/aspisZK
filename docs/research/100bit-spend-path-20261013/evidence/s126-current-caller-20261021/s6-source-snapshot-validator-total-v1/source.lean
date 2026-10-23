import S6SourceCanonicalTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.SnapshotTotal
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_tree_profile

theorem canonical_eq (digest : Array U32 8#usize) :
    digest_is_canonical digest =
      aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical digest := by
  rfl

@[step] theorem canonical_spec (digest : Array U32 8#usize) :
    digest_is_canonical digest ⦃ _ => True ⦄ := by
  rw [canonical_eq]
  obtain ⟨value,h⟩ := CanonicalTotal.scan_total digest
  rw [h,WP.spec_ok]
  trivial

/-- TOTAL closed reference validator on the complete native snapshot carrier.
Malformed inputs return ordinary Rust errors; no successful-child premise. -/
theorem snapshot_total (snapshot : PoolV1PairLiveSnapshotV1) :
    ∃ out, validate_pool_v1_pair_live_snapshot_v1 snapshot=ok out := by
  have hw : validate_pool_v1_pair_live_snapshot_v1 snapshot ⦃ _ => True ⦄ := by
    unfold validate_pool_v1_pair_live_snapshot_v1
    step*
    all_goals scalar_tac
  obtain ⟨value,h,_⟩ := spec_imp_exists hw
  exact ⟨value,h⟩

#print axioms canonical_eq
#print axioms canonical_spec
#print axioms snapshot_total
end AspisS6SourceCodec.SnapshotTotal
