import RPz7_S6NativeAfterstateCodecV1
import S6StdByteArrayTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotValidatorTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem frontier_spec (frontier : Array (Array U32 8#usize) 20#usize)
    (level : Usize) (bound : level.val≤20) :
    validate_pool_v1_pair_live_snapshot_v1_loop frontier level ⦃ _ => True ⦄ := by
  unfold validate_pool_v1_pair_live_snapshot_v1_loop
  refine loop.spec_decr_nat
    (fun i : Usize => 20-i.val) (fun i : Usize => i.val≤20)
    (fun _ => True)
    (fun i => validate_pool_v1_pair_live_snapshot_v1_loop.body frontier i) level ?_ bound
  intro i hi
  unfold validate_pool_v1_pair_live_snapshot_v1_loop.body
  step*
  all_goals scalar_tac

@[step] theorem validator_spec (snapshot : PoolV1PairLiveSnapshotV1) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot
      ⦃ result => validate_pool_v1_pair_live_snapshot_v1 snapshot=ok result ⦄ := by
  have total : validate_pool_v1_pair_live_snapshot_v1 snapshot ⦃ _ => True ⦄ := by
    unfold validate_pool_v1_pair_live_snapshot_v1 POOL_V1_PAIR_CAPACITY
      POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
    step*
    all_goals scalar_tac
  obtain ⟨result,run,_⟩ := spec_imp_exists total
  apply exists_imp_spec
  exact ⟨result,run,run⟩

#print axioms frontier_spec
#print axioms validator_spec
end AspisS6NativeSnapshotValidatorTotal
