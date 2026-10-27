import R1Z.PDict_ReachErase04
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.sample_source_d_loop`. -/
theorem erase_80 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.sample_source_d_loop _ (replace ops other) = @aspis_prover.state_only_entropy.sample_source_d_loop _ ops := by
  delta aspis_prover.state_only_entropy.sample_source_d_loop
  first | rfl | (try simp only [erase_79 ops other]; all_goals rfl)
#print axioms erase_80

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.sample_source_d`. -/
theorem erase_81 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.sample_source_d _ (replace ops other) = @aspis_prover.state_only_entropy.sample_source_d _ ops := by
  delta aspis_prover.state_only_entropy.sample_source_d
  first | rfl | (try simp only [erase_80 ops other]; all_goals rfl)
#print axioms erase_81

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d`. -/
theorem erase_82 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d _ (replace ops other) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d _ ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
  first | rfl | (try simp only [erase_62 ops other, erase_63 ops other, erase_65 ops other, erase_67 ops other, erase_72 ops other, erase_73 ops other, erase_81 ops other, erase_64 ops other]; all_goals rfl)
#print axioms erase_82

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d`. -/
theorem erase_83 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d _ (replace ops other) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d _ ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
  first | rfl | (try simp only [erase_82 ops other]; all_goals rfl)
#print axioms erase_83

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref`. -/
theorem erase_84 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref _ (replace ops other) = @aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref _ ops := by
  delta aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref
  all_goals rfl
#print axioms erase_84

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.inactive_m31_step`. -/
theorem erase_85 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.inactive_m31_step _ (replace ops other) = @aspis_prover.state_only_hiding.inactive_m31_step _ ops := by
  delta aspis_prover.state_only_hiding.inactive_m31_step
  all_goals rfl
#print axioms erase_85

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body`. -/
theorem erase_86 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body
  first | rfl | (try simp only [erase_85 ops other]; all_goals rfl)
#print axioms erase_86

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop`. -/
theorem erase_87 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop _ (replace ops other) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop _ ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop
  first | rfl | (try simp only [erase_86 ops other]; all_goals rfl)
#print axioms erase_87

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_m31_copy_inactive`. -/
theorem erase_88 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive _ (replace ops other) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive _ ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive
  first | rfl | (try simp only [erase_87 ops other]; all_goals rfl)
#print axioms erase_88

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.balance_m31_copy_inactive`. -/
theorem erase_89 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.balance_m31_copy_inactive _ (replace ops other) = @aspis_prover.state_only_hiding.balance_m31_copy_inactive _ ops := by
  delta aspis_prover.state_only_hiding.balance_m31_copy_inactive
  first | rfl | (try simp only [erase_88 ops other]; all_goals rfl)
#print axioms erase_89

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_columns_from`. -/
theorem erase_90 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_columns_from _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_columns_from _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_columns_from
  first | rfl | (try simp only [erase_89 ops other]; all_goals rfl)
#print axioms erase_90

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_columns`. -/
theorem erase_91 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_columns _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_columns _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_columns
  first | rfl | (try simp only [erase_63 ops other, erase_90 ops other]; all_goals rfl)
#print axioms erase_91

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.SeedExpander.qm31`. -/
theorem erase_92 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.SeedExpander.qm31 _ (replace ops other) = @aspis_prover.state_only_hiding.SeedExpander.qm31 _ ops := by
  delta aspis_prover.state_only_hiding.SeedExpander.qm31
  all_goals rfl
#print axioms erase_92

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.inactive_qm31_step`. -/
theorem erase_93 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.inactive_qm31_step _ (replace ops other) = @aspis_prover.state_only_hiding.inactive_qm31_step _ ops := by
  delta aspis_prover.state_only_hiding.inactive_qm31_step
  all_goals rfl
#print axioms erase_93

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body`. -/
theorem erase_94 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body
  first | rfl | (try simp only [erase_93 ops other]; all_goals rfl)
#print axioms erase_94

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop`. -/
theorem erase_95 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop _ (replace ops other) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop _ ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop
  first | rfl | (try simp only [erase_94 ops other]; all_goals rfl)
#print axioms erase_95
end R1Z.PDict_ReachErase
