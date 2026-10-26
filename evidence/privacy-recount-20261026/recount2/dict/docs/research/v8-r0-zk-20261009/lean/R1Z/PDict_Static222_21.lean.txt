import R1Z.PDict_Static222_20
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `prover.audit_masks`. -/
theorem erase_336 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.audit_masks (types base F) (selected base F ops) = @prover.audit_masks base ops := by
  delta prover.audit_masks
  try simp only [erase_330 base F ops, erase_332 base F ops, erase_335 base F ops]
  all_goals rfl
#print axioms erase_336

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt`. -/
theorem erase_337 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt base ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
  try simp only [erase_62 base F ops, erase_67 base F ops, erase_73 base F ops, erase_64 base F ops]
  all_goals rfl
#print axioms erase_337

/-- Carrier transport candidate for `prover.derive_private_salt_step`. -/
theorem erase_338 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.derive_private_salt_step (types base F) (selected base F ops) = @prover.derive_private_salt_step base ops := by
  delta prover.derive_private_salt_step
  try simp only [erase_337 base F ops]
  all_goals rfl
#print axioms erase_338

/-- Carrier transport candidate for `prover.derive_private_salts_loop.body`. -/
theorem erase_339 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.derive_private_salts_loop.body (types base F) (selected base F ops) = @prover.derive_private_salts_loop.body base ops := by
  delta prover.derive_private_salts_loop.body
  try simp only [erase_338 base F ops]
  all_goals rfl
#print axioms erase_339

/-- Carrier transport candidate for `prover.derive_private_salts_loop`. -/
theorem erase_340 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.derive_private_salts_loop (types base F) (selected base F ops) = @prover.derive_private_salts_loop base ops := by
  delta prover.derive_private_salts_loop
  try simp only [erase_339 base F ops]
  all_goals rfl
#print axioms erase_340

/-- Carrier transport candidate for `prover.derive_private_salts`. -/
theorem erase_341 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.derive_private_salts (types base F) (selected base F ops) = @prover.derive_private_salts base ops := by
  delta prover.derive_private_salts
  try simp only [erase_340 base F ops]
  all_goals rfl
#print axioms erase_341

/-- Carrier transport candidate for `prover.fixed_k_column`. -/
theorem erase_342 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.fixed_k_column (types base F) (selected base F ops) = @prover.fixed_k_column base ops := by
  delta prover.fixed_k_column
  all_goals rfl
#print axioms erase_342

/-- Carrier transport candidate for `host_transcript.trace_queries_loop.body`. -/
theorem erase_343 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.trace_queries_loop.body (types base F) (selected base F ops) = @host_transcript.trace_queries_loop.body base ops := by
  delta host_transcript.trace_queries_loop.body
  all_goals rfl
#print axioms erase_343

/-- Carrier transport candidate for `host_transcript.trace_queries_loop`. -/
theorem erase_344 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.trace_queries_loop (types base F) (selected base F ops) = @host_transcript.trace_queries_loop base ops := by
  delta host_transcript.trace_queries_loop
  try simp only [erase_343 base F ops]
  all_goals rfl
#print axioms erase_344

/-- Carrier transport candidate for `host_transcript.trace_queries`. -/
theorem erase_345 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.trace_queries (types base F) (selected base F ops) = @host_transcript.trace_queries base ops := by
  delta host_transcript.trace_queries
  try simp only [erase_344 base F ops]
  all_goals rfl
#print axioms erase_345

/-- Carrier transport candidate for `host_transcript.Transcript.queries`. -/
theorem erase_346 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.Transcript.queries (types base F) (selected base F ops) = @host_transcript.Transcript.queries base ops := by
  delta host_transcript.Transcript.queries
  try simp only [erase_345 base F ops]
  all_goals rfl
#print axioms erase_346

/-- Carrier transport candidate for `host_transcript.Transcript.scalar`. -/
theorem erase_347 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.Transcript.scalar (types base F) (selected base F ops) = @host_transcript.Transcript.scalar base ops := by
  delta host_transcript.Transcript.scalar
  all_goals rfl
#print axioms erase_347

/-- Carrier transport candidate for `host_transcript.Transcript.scalar_k`. -/
theorem erase_348 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.Transcript.scalar_k (types base F) (selected base F ops) = @host_transcript.Transcript.scalar_k base ops := by
  delta host_transcript.Transcript.scalar_k
  all_goals rfl
#print axioms erase_348

/-- Carrier transport candidate for `prover.encoded_slice_loop.body`. -/
theorem erase_349 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.encoded_slice_loop.body (types base F) (selected base F ops) = @prover.encoded_slice_loop.body base ops := by
  delta prover.encoded_slice_loop.body
  all_goals rfl
#print axioms erase_349

/-- Carrier transport candidate for `prover.encoded_slice_loop`. -/
theorem erase_350 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.encoded_slice_loop (types base F) (selected base F ops) = @prover.encoded_slice_loop base ops := by
  delta prover.encoded_slice_loop
  try simp only [erase_349 base F ops]
  all_goals rfl
#print axioms erase_350

/-- Carrier transport candidate for `prover.encoded_slice`. -/
theorem erase_351 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.encoded_slice (types base F) (selected base F ops) = @prover.encoded_slice base ops := by
  delta prover.encoded_slice
  try simp only [erase_350 base F ops]
  all_goals rfl
#print axioms erase_351
end R1Z.PDict_Static222
