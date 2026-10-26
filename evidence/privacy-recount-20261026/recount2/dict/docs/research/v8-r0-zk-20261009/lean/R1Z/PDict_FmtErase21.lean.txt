import R1Z.PDict_FmtErase20
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.audit_masks`. -/
theorem erase_336 (ops other : ExternalFuns) :
    @prover.audit_masks _ (replace ops other) = @prover.audit_masks _ ops := by
  delta prover.audit_masks
  try simp only [erase_330 ops other, erase_332 ops other, erase_335 ops other]
  all_goals rfl
#print axioms erase_336

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt`. -/
theorem erase_337 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt _ (replace ops other) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt _ ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
  try simp only [erase_62 ops other, erase_67 ops other, erase_73 ops other, erase_64 ops other]
  all_goals rfl
#print axioms erase_337

/-- Full symbolic source-function equality for `prover.derive_private_salt_step`. -/
theorem erase_338 (ops other : ExternalFuns) :
    @prover.derive_private_salt_step _ (replace ops other) = @prover.derive_private_salt_step _ ops := by
  delta prover.derive_private_salt_step
  try simp only [erase_337 ops other]
  all_goals rfl
#print axioms erase_338

/-- Full symbolic source-function equality for `prover.derive_private_salts_loop.body`. -/
theorem erase_339 (ops other : ExternalFuns) :
    @prover.derive_private_salts_loop.body _ (replace ops other) = @prover.derive_private_salts_loop.body _ ops := by
  delta prover.derive_private_salts_loop.body
  try simp only [erase_338 ops other]
  all_goals rfl
#print axioms erase_339

/-- Full symbolic source-function equality for `prover.derive_private_salts_loop`. -/
theorem erase_340 (ops other : ExternalFuns) :
    @prover.derive_private_salts_loop _ (replace ops other) = @prover.derive_private_salts_loop _ ops := by
  delta prover.derive_private_salts_loop
  try simp only [erase_339 ops other]
  all_goals rfl
#print axioms erase_340

/-- Full symbolic source-function equality for `prover.derive_private_salts`. -/
theorem erase_341 (ops other : ExternalFuns) :
    @prover.derive_private_salts _ (replace ops other) = @prover.derive_private_salts _ ops := by
  delta prover.derive_private_salts
  try simp only [erase_340 ops other]
  all_goals rfl
#print axioms erase_341

/-- Full symbolic source-function equality for `prover.fixed_k_column`. -/
theorem erase_342 (ops other : ExternalFuns) :
    @prover.fixed_k_column _ (replace ops other) = @prover.fixed_k_column _ ops := by
  delta prover.fixed_k_column
  all_goals rfl
#print axioms erase_342

/-- Full symbolic source-function equality for `host_transcript.trace_queries_loop.body`. -/
theorem erase_343 (ops other : ExternalFuns) :
    @host_transcript.trace_queries_loop.body _ (replace ops other) = @host_transcript.trace_queries_loop.body _ ops := by
  delta host_transcript.trace_queries_loop.body
  all_goals rfl
#print axioms erase_343

/-- Full symbolic source-function equality for `host_transcript.trace_queries_loop`. -/
theorem erase_344 (ops other : ExternalFuns) :
    @host_transcript.trace_queries_loop _ (replace ops other) = @host_transcript.trace_queries_loop _ ops := by
  delta host_transcript.trace_queries_loop
  try simp only [erase_343 ops other]
  all_goals rfl
#print axioms erase_344

/-- Full symbolic source-function equality for `host_transcript.trace_queries`. -/
theorem erase_345 (ops other : ExternalFuns) :
    @host_transcript.trace_queries _ (replace ops other) = @host_transcript.trace_queries _ ops := by
  delta host_transcript.trace_queries
  try simp only [erase_344 ops other]
  all_goals rfl
#print axioms erase_345

/-- Full symbolic source-function equality for `host_transcript.Transcript.queries`. -/
theorem erase_346 (ops other : ExternalFuns) :
    @host_transcript.Transcript.queries _ (replace ops other) = @host_transcript.Transcript.queries _ ops := by
  delta host_transcript.Transcript.queries
  try simp only [erase_345 ops other]
  all_goals rfl
#print axioms erase_346

/-- Full symbolic source-function equality for `host_transcript.Transcript.scalar`. -/
theorem erase_347 (ops other : ExternalFuns) :
    @host_transcript.Transcript.scalar _ (replace ops other) = @host_transcript.Transcript.scalar _ ops := by
  delta host_transcript.Transcript.scalar
  all_goals rfl
#print axioms erase_347

/-- Full symbolic source-function equality for `host_transcript.Transcript.scalar_k`. -/
theorem erase_348 (ops other : ExternalFuns) :
    @host_transcript.Transcript.scalar_k _ (replace ops other) = @host_transcript.Transcript.scalar_k _ ops := by
  delta host_transcript.Transcript.scalar_k
  all_goals rfl
#print axioms erase_348

/-- Full symbolic source-function equality for `prover.encoded_slice_loop.body`. -/
theorem erase_349 (ops other : ExternalFuns) :
    @prover.encoded_slice_loop.body _ (replace ops other) = @prover.encoded_slice_loop.body _ ops := by
  delta prover.encoded_slice_loop.body
  all_goals rfl
#print axioms erase_349

/-- Full symbolic source-function equality for `prover.encoded_slice_loop`. -/
theorem erase_350 (ops other : ExternalFuns) :
    @prover.encoded_slice_loop _ (replace ops other) = @prover.encoded_slice_loop _ ops := by
  delta prover.encoded_slice_loop
  try simp only [erase_349 ops other]
  all_goals rfl
#print axioms erase_350

/-- Full symbolic source-function equality for `prover.encoded_slice`. -/
theorem erase_351 (ops other : ExternalFuns) :
    @prover.encoded_slice _ (replace ops other) = @prover.encoded_slice _ ops := by
  delta prover.encoded_slice
  try simp only [erase_350 ops other]
  all_goals rfl
#print axioms erase_351
end R1Z.PDict_FmtErase
