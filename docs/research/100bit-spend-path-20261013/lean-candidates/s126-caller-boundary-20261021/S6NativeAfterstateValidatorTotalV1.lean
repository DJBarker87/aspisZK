import S6NativeWordSourceBindingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateValidatorTotal
open AspisR1TerminalDecoder

@[step] theorem canonical_spec (digest : Array U32 8#usize) :
    pool_v1.pair_tree_profile.digest_is_canonical digest ⦃ _ => True ⦄ := by
  unfold pool_v1.pair_tree_profile.digest_is_canonical
    pool_v1.pair_tree_profile.digest_is_canonical_loop
  refine loop.spec_decr_nat
    (fun i : Usize => 8-i.val) (fun i : Usize => i.val≤8)
    (fun _ : Bool => True)
    (fun i => pool_v1.pair_tree_profile.digest_is_canonical_loop.body digest i) 0#usize ?_ ?_
  · intro i hi
    unfold pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    step*
    all_goals scalar_tac
  · scalar_tac

@[step] theorem frontier_spec (frontier : Array (Array U32 8#usize) 20#usize)
    (level : Usize) (bound : level.val≤20) :
    pool_v1.pair_terminal.validate_verified_afterstate_loop frontier level ⦃ _ => True ⦄ := by
  unfold pool_v1.pair_terminal.validate_verified_afterstate_loop
  refine loop.spec_decr_nat
    (fun i : Usize => 20-i.val) (fun i : Usize => i.val≤20)
    (fun _ => True)
    (fun i => pool_v1.pair_terminal.validate_verified_afterstate_loop.body frontier i) level ?_ bound
  intro i hi
  unfold pool_v1.pair_terminal.validate_verified_afterstate_loop.body
  step*
  all_goals scalar_tac

@[step] theorem validator_spec (afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    pool_v1.pair_terminal.validate_verified_afterstate afterstate
      ⦃ result => pool_v1.pair_terminal.validate_verified_afterstate afterstate=ok result ⦄ := by
  have total : pool_v1.pair_terminal.validate_verified_afterstate afterstate ⦃ _ => True ⦄ := by
    unfold pool_v1.pair_terminal.validate_verified_afterstate
      pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
    step*
    all_goals scalar_tac
  obtain ⟨result,run,_⟩ := spec_imp_exists total
  apply exists_imp_spec
  exact ⟨result,run,run⟩

#print axioms canonical_spec
#print axioms frontier_spec
#print axioms validator_spec
end AspisS6NativeAfterstateValidatorTotal
