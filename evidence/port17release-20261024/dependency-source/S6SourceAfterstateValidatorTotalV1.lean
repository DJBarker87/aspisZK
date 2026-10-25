import S6SourceSnapshotValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateTotal
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

/-- TOTAL complete reference validator; all twenty frontier entries and exact
ordinary error branches are retained, without successful-child premises. -/
theorem afterstate_total (afterstate : PoolV1PairVerifiedAfterstateV1) :
    ∃ out, validate_verified_afterstate afterstate=ok out := by
  have hw : validate_verified_afterstate afterstate ⦃ _ => True ⦄ := by
    unfold validate_verified_afterstate
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
    step*
    all_goals scalar_tac
  obtain ⟨value,h,_⟩ := spec_imp_exists hw
  exact ⟨value,h⟩

#print axioms afterstate_total
end AspisS6SourceCodec.AfterstateTotal
