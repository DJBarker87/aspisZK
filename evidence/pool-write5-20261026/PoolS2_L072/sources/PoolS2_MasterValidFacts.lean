import PoolS2_MasterValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterValidFacts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation

def Valid (m : Master) : Prop :=
  m.identity.pool ≠ PoolS2_PolicyFacts.zero ∧
  m.identity.asset_mint ≠ PoolS2_PolicyFacts.zero ∧
  m.identity.token_program ≠ PoolS2_PolicyFacts.zero ∧
  m.identity.deployment_domain ≠ PoolS2_PolicyFacts.zero ∧
  PoolS2_PolicyFacts.Valid m.verifier_policy ∧
  (∀ s ∈ m.last_checkpoint_lane_sequences.val, s ≤ capacity) ∧
  (m.has_checkpoint = true → m.next_checkpoint_sequence ≠ 0#u64) ∧
  (m.has_checkpoint = false → m.next_checkpoint_sequence = 0#u64 ∧
    m.last_checkpoint_lane_sequences = Array.repeat 8#usize 0#u64)

theorem accepted (m : Master) (h : run m = ok (.Ok ())) : Valid m := by
  classical
  unfold Valid
  unfold run at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals have policy := PoolS2_PolicyFacts.accepted m.verifier_policy (by assumption)
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_MasterValidFacts
end
