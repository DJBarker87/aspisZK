import R1Z.PDict_Static222_19
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body`. -/
theorem erase_320 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body
  all_goals rfl
#print axioms erase_320

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0`. -/
theorem erase_321 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
  try simp only [erase_320 base F ops]
  all_goals rfl
#print axioms erase_321

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body`. -/
theorem erase_322 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body
  all_goals rfl
#print axioms erase_322

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1`. -/
theorem erase_323 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1
  try simp only [erase_322 base F ops]
  all_goals rfl
#print axioms erase_323

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2`. -/
theorem erase_324 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
  try simp only [erase_310 base F ops, erase_312 base F ops, erase_321 base F ops, erase_323 base F ops]
  all_goals rfl
#print axioms erase_324

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments`. -/
theorem erase_325 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
  try simp only [erase_319 base F ops, erase_324 base F ops]
  all_goals rfl
#print axioms erase_325

/-- Carrier transport candidate for `prover.inactive_sum_m31_loop.body`. -/
theorem erase_326 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_m31_loop.body (types base F) (selected base F ops) = @prover.inactive_sum_m31_loop.body base ops := by
  delta prover.inactive_sum_m31_loop.body
  all_goals rfl
#print axioms erase_326

/-- Carrier transport candidate for `prover.inactive_sum_m31_loop`. -/
theorem erase_327 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_m31_loop (types base F) (selected base F ops) = @prover.inactive_sum_m31_loop base ops := by
  delta prover.inactive_sum_m31_loop
  try simp only [erase_326 base F ops]
  all_goals rfl
#print axioms erase_327

/-- Carrier transport candidate for `prover.inactive_sum_m31`. -/
theorem erase_328 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_m31 (types base F) (selected base F ops) = @prover.inactive_sum_m31 base ops := by
  delta prover.inactive_sum_m31
  try simp only [erase_327 base F ops]
  all_goals rfl
#print axioms erase_328

/-- Carrier transport candidate for `prover.audit_masks_loop0.body`. -/
theorem erase_329 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.audit_masks_loop0.body (types base F) (selected base F ops) = @prover.audit_masks_loop0.body base ops := by
  delta prover.audit_masks_loop0.body
  try simp only [erase_328 base F ops]
  all_goals rfl
#print axioms erase_329

/-- Carrier transport candidate for `prover.audit_masks_loop0`. -/
theorem erase_330 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.audit_masks_loop0 (types base F) (selected base F ops) = @prover.audit_masks_loop0 base ops := by
  delta prover.audit_masks_loop0
  try simp only [erase_329 base F ops]
  all_goals rfl
#print axioms erase_330

/-- Carrier transport candidate for `prover.audit_masks_loop1.body`. -/
theorem erase_331 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.audit_masks_loop1.body (types base F) (selected base F ops) = @prover.audit_masks_loop1.body base ops := by
  delta prover.audit_masks_loop1.body
  try simp only [erase_328 base F ops]
  all_goals rfl
#print axioms erase_331

/-- Carrier transport candidate for `prover.audit_masks_loop1`. -/
theorem erase_332 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.audit_masks_loop1 (types base F) (selected base F ops) = @prover.audit_masks_loop1 base ops := by
  delta prover.audit_masks_loop1
  try simp only [erase_331 base F ops]
  all_goals rfl
#print axioms erase_332

/-- Carrier transport candidate for `prover.inactive_sum_k_loop.body`. -/
theorem erase_333 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_k_loop.body (types base F) (selected base F ops) = @prover.inactive_sum_k_loop.body base ops := by
  delta prover.inactive_sum_k_loop.body
  all_goals rfl
#print axioms erase_333

/-- Carrier transport candidate for `prover.inactive_sum_k_loop`. -/
theorem erase_334 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_k_loop (types base F) (selected base F ops) = @prover.inactive_sum_k_loop base ops := by
  delta prover.inactive_sum_k_loop
  try simp only [erase_333 base F ops]
  all_goals rfl
#print axioms erase_334

/-- Carrier transport candidate for `prover.inactive_sum_k`. -/
theorem erase_335 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.inactive_sum_k (types base F) (selected base F ops) = @prover.inactive_sum_k base ops := by
  delta prover.inactive_sum_k
  try simp only [erase_334 base F ops]
  all_goals rfl
#print axioms erase_335
end R1Z.PDict_Static222
