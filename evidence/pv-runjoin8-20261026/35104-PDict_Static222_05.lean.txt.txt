import R1Z.PDict_Static222_04
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `aspis_prover.state_only_entropy.sample_source_d_loop`. -/
theorem erase_80 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.sample_source_d_loop (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.sample_source_d_loop base ops := by
  delta aspis_prover.state_only_entropy.sample_source_d_loop
  first | rfl | (try simp only [erase_79 base F ops]; all_goals rfl)
#print axioms erase_80

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.sample_source_d`. -/
theorem erase_81 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.sample_source_d (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.sample_source_d base ops := by
  delta aspis_prover.state_only_entropy.sample_source_d
  first | rfl | (try simp only [erase_80 base F ops]; all_goals rfl)
#print axioms erase_81

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d`. -/
theorem erase_82 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d base ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
  first | rfl | (try simp only [erase_62 base F ops, erase_63 base F ops, erase_65 base F ops, erase_67 base F ops, erase_72 base F ops, erase_73 base F ops, erase_81 base F ops, erase_64 base F ops]; all_goals rfl)
#print axioms erase_82

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d`. -/
theorem erase_83 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d base ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
  first | rfl | (try simp only [erase_82 base F ops]; all_goals rfl)
#print axioms erase_83

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref`. -/
theorem erase_84 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref base ops := by
  delta aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref
  all_goals rfl
#print axioms erase_84

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.inactive_m31_step`. -/
theorem erase_85 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.inactive_m31_step (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.inactive_m31_step base ops := by
  delta aspis_prover.state_only_hiding.inactive_m31_step
  all_goals rfl
#print axioms erase_85

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body`. -/
theorem erase_86 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body base ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body
  first | rfl | (try simp only [erase_85 base F ops]; all_goals rfl)
#print axioms erase_86

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop`. -/
theorem erase_87 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop base ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop
  first | rfl | (try simp only [erase_86 base F ops]; all_goals rfl)
#print axioms erase_87

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_m31_copy_inactive`. -/
theorem erase_88 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_m31_copy_inactive (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_m31_copy_inactive base ops := by
  delta aspis_prover.state_only_hiding.sum_m31_copy_inactive
  first | rfl | (try simp only [erase_87 base F ops]; all_goals rfl)
#print axioms erase_88

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.balance_m31_copy_inactive`. -/
theorem erase_89 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.balance_m31_copy_inactive (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.balance_m31_copy_inactive base ops := by
  delta aspis_prover.state_only_hiding.balance_m31_copy_inactive
  first | rfl | (try simp only [erase_88 base F ops]; all_goals rfl)
#print axioms erase_89

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_columns_from`. -/
theorem erase_90 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_columns_from (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_columns_from base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_columns_from
  first | rfl | (try simp only [erase_89 base F ops]; all_goals rfl)
#print axioms erase_90

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_columns`. -/
theorem erase_91 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_columns (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_columns base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_columns
  first | rfl | (try simp only [erase_63 base F ops, erase_90 base F ops]; all_goals rfl)
#print axioms erase_91

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.SeedExpander.qm31`. -/
theorem erase_92 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.SeedExpander.qm31 (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.SeedExpander.qm31 base ops := by
  delta aspis_prover.state_only_hiding.SeedExpander.qm31
  all_goals rfl
#print axioms erase_92

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.inactive_qm31_step`. -/
theorem erase_93 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.inactive_qm31_step (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.inactive_qm31_step base ops := by
  delta aspis_prover.state_only_hiding.inactive_qm31_step
  all_goals rfl
#print axioms erase_93

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body`. -/
theorem erase_94 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body base ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop.body
  first | rfl | (try simp only [erase_93 base F ops]; all_goals rfl)
#print axioms erase_94

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop`. -/
theorem erase_95 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop base ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive_loop
  first | rfl | (try simp only [erase_94 base F ops]; all_goals rfl)
#print axioms erase_95
end R1Z.PDict_Static222
