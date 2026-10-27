import R1Z.PDict_FmtErase19
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body`. -/
theorem erase_320 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body
  all_goals rfl
#print axioms erase_320

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0`. -/
theorem erase_321 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
  try simp only [erase_320 ops other]
  all_goals rfl
#print axioms erase_321

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body`. -/
theorem erase_322 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body
  all_goals rfl
#print axioms erase_322

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1`. -/
theorem erase_323 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1
  try simp only [erase_322 ops other]
  all_goals rfl
#print axioms erase_323

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2`. -/
theorem erase_324 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
  try simp only [erase_310 ops other, erase_312 ops other, erase_321 ops other, erase_323 ops other]
  all_goals rfl
#print axioms erase_324

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments`. -/
theorem erase_325 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
  try simp only [erase_319 ops other, erase_324 ops other]
  all_goals rfl
#print axioms erase_325

/-- Full symbolic source-function equality for `prover.inactive_sum_m31_loop.body`. -/
theorem erase_326 (ops other : ExternalFuns) :
    @prover.inactive_sum_m31_loop.body _ (replace ops other) = @prover.inactive_sum_m31_loop.body _ ops := by
  delta prover.inactive_sum_m31_loop.body
  all_goals rfl
#print axioms erase_326

/-- Full symbolic source-function equality for `prover.inactive_sum_m31_loop`. -/
theorem erase_327 (ops other : ExternalFuns) :
    @prover.inactive_sum_m31_loop _ (replace ops other) = @prover.inactive_sum_m31_loop _ ops := by
  delta prover.inactive_sum_m31_loop
  try simp only [erase_326 ops other]
  all_goals rfl
#print axioms erase_327

/-- Full symbolic source-function equality for `prover.inactive_sum_m31`. -/
theorem erase_328 (ops other : ExternalFuns) :
    @prover.inactive_sum_m31 _ (replace ops other) = @prover.inactive_sum_m31 _ ops := by
  delta prover.inactive_sum_m31
  try simp only [erase_327 ops other]
  all_goals rfl
#print axioms erase_328

/-- Full symbolic source-function equality for `prover.audit_masks_loop0.body`. -/
theorem erase_329 (ops other : ExternalFuns) :
    @prover.audit_masks_loop0.body _ (replace ops other) = @prover.audit_masks_loop0.body _ ops := by
  delta prover.audit_masks_loop0.body
  try simp only [erase_328 ops other]
  all_goals rfl
#print axioms erase_329

/-- Full symbolic source-function equality for `prover.audit_masks_loop0`. -/
theorem erase_330 (ops other : ExternalFuns) :
    @prover.audit_masks_loop0 _ (replace ops other) = @prover.audit_masks_loop0 _ ops := by
  delta prover.audit_masks_loop0
  try simp only [erase_329 ops other]
  all_goals rfl
#print axioms erase_330

/-- Full symbolic source-function equality for `prover.audit_masks_loop1.body`. -/
theorem erase_331 (ops other : ExternalFuns) :
    @prover.audit_masks_loop1.body _ (replace ops other) = @prover.audit_masks_loop1.body _ ops := by
  delta prover.audit_masks_loop1.body
  try simp only [erase_328 ops other]
  all_goals rfl
#print axioms erase_331

/-- Full symbolic source-function equality for `prover.audit_masks_loop1`. -/
theorem erase_332 (ops other : ExternalFuns) :
    @prover.audit_masks_loop1 _ (replace ops other) = @prover.audit_masks_loop1 _ ops := by
  delta prover.audit_masks_loop1
  try simp only [erase_331 ops other]
  all_goals rfl
#print axioms erase_332

/-- Full symbolic source-function equality for `prover.inactive_sum_k_loop.body`. -/
theorem erase_333 (ops other : ExternalFuns) :
    @prover.inactive_sum_k_loop.body _ (replace ops other) = @prover.inactive_sum_k_loop.body _ ops := by
  delta prover.inactive_sum_k_loop.body
  all_goals rfl
#print axioms erase_333

/-- Full symbolic source-function equality for `prover.inactive_sum_k_loop`. -/
theorem erase_334 (ops other : ExternalFuns) :
    @prover.inactive_sum_k_loop _ (replace ops other) = @prover.inactive_sum_k_loop _ ops := by
  delta prover.inactive_sum_k_loop
  try simp only [erase_333 ops other]
  all_goals rfl
#print axioms erase_334

/-- Full symbolic source-function equality for `prover.inactive_sum_k`. -/
theorem erase_335 (ops other : ExternalFuns) :
    @prover.inactive_sum_k _ (replace ops other) = @prover.inactive_sum_k _ ops := by
  delta prover.inactive_sum_k
  try simp only [erase_334 ops other]
  all_goals rfl
#print axioms erase_335
end R1Z.PDict_FmtErase
