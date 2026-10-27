import R1Z.PDict_Static222_22B
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `prover.round_loop0`. -/
theorem erase_368 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0 (types base F) (selected base F ops) = @prover.round_loop0 base ops := by
  delta prover.round_loop0
  try simp only [erase_367 base F ops]
  all_goals rfl
#print axioms erase_368

/-- Carrier transport candidate for `prover.round_loop1.body`. -/
theorem erase_369 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop1.body (types base F) (selected base F ops) = @prover.round_loop1.body base ops := by
  delta prover.round_loop1.body
  all_goals rfl
#print axioms erase_369

/-- Carrier transport candidate for `prover.round_loop1`. -/
theorem erase_370 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop1 (types base F) (selected base F ops) = @prover.round_loop1 base ops := by
  delta prover.round_loop1
  try simp only [erase_369 base F ops]
  all_goals rfl
#print axioms erase_370

/-- Carrier transport candidate for `prover.round`. -/
theorem erase_371 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round (types base F) (selected base F ops) = @prover.round base ops := by
  delta prover.round
  try simp only [erase_368 base F ops, erase_370 base F ops]
  all_goals rfl
#print axioms erase_371

/-- Carrier transport candidate for `prover.finish_opening`. -/
theorem erase_372 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.finish_opening (types base F) (selected base F ops) = @prover.finish_opening base ops := by
  delta prover.finish_opening
  try simp only [erase_59 base F ops, erase_346 base F ops, erase_347 base F ops, erase_348 base F ops, erase_308 base F ops, erase_311 base F ops, erase_351 base F ops, erase_355 base F ops, erase_360 base F ops, erase_362 base F ops, erase_371 base F ops]
  all_goals rfl
#print axioms erase_372

/-- Carrier transport candidate for `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact`. -/
theorem erase_373 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact (types base F) (selected base F ops) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact base ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
  all_goals rfl
#print axioms erase_373

/-- Carrier transport candidate for `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq`. -/
theorem erase_374 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq (types base F) (selected base F ops) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq base ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq
  try simp only [erase_373 base F ops]
  all_goals rfl
#print axioms erase_374

/-- Carrier transport candidate for `aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField`. -/
theorem erase_375 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base F) (selected base F ops) = @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField base ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
  try simp only [erase_374 base F ops, erase_273 base F ops]
  all_goals rfl
#print axioms erase_375

/-- Carrier transport candidate for `host_transcript.Transcript.new`. -/
theorem erase_376 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_transcript.Transcript.new (types base F) (selected base F ops) = @host_transcript.Transcript.new base ops := by
  delta host_transcript.Transcript.new
  all_goals rfl
#print axioms erase_376

/-- Carrier transport candidate for `prover.opening_row_loop.body`. -/
theorem erase_377 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_row_loop.body (types base F) (selected base F ops) = @prover.opening_row_loop.body base ops := by
  delta prover.opening_row_loop.body
  all_goals rfl
#print axioms erase_377

/-- Carrier transport candidate for `prover.opening_row_loop`. -/
theorem erase_378 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_row_loop (types base F) (selected base F ops) = @prover.opening_row_loop base ops := by
  delta prover.opening_row_loop
  try simp only [erase_377 base F ops]
  all_goals rfl
#print axioms erase_378

/-- Carrier transport candidate for `prover.opening_row`. -/
theorem erase_379 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_row (types base F) (selected base F ops) = @prover.opening_row base ops := by
  delta prover.opening_row
  try simp only [erase_378 base F ops]
  all_goals rfl
#print axioms erase_379

/-- Carrier transport candidate for `prover.opening_batch_loop.body`. -/
theorem erase_380 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_batch_loop.body (types base F) (selected base F ops) = @prover.opening_batch_loop.body base ops := by
  delta prover.opening_batch_loop.body
  try simp only [erase_379 base F ops]
  all_goals rfl
#print axioms erase_380

/-- Carrier transport candidate for `prover.opening_batch_loop`. -/
theorem erase_381 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_batch_loop (types base F) (selected base F ops) = @prover.opening_batch_loop base ops := by
  delta prover.opening_batch_loop
  try simp only [erase_380 base F ops]
  all_goals rfl
#print axioms erase_381

/-- Carrier transport candidate for `prover.opening_batch`. -/
theorem erase_382 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_batch (types base F) (selected base F ops) = @prover.opening_batch base ops := by
  delta prover.opening_batch
  try simp only [erase_381 base F ops]
  all_goals rfl
#print axioms erase_382

/-- Carrier transport candidate for `prover.opening_claim_bytes_loop.body`. -/
theorem erase_383 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.opening_claim_bytes_loop.body (types base F) (selected base F ops) = @prover.opening_claim_bytes_loop.body base ops := by
  delta prover.opening_claim_bytes_loop.body
  try simp only [erase_375 base F ops]
  all_goals rfl
#print axioms erase_383
end R1Z.PDict_Static222
