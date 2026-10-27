import R1Z.PDict_ReachErase22B
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.round_loop0`. -/
theorem erase_368 (ops other : ExternalFuns) :
    @prover.round_loop0 _ (replace ops other) = @prover.round_loop0 _ ops := by
  delta prover.round_loop0
  try simp only [erase_367 ops other]
  all_goals rfl
#print axioms erase_368

/-- Full symbolic source-function equality for `prover.round_loop1.body`. -/
theorem erase_369 (ops other : ExternalFuns) :
    @prover.round_loop1.body _ (replace ops other) = @prover.round_loop1.body _ ops := by
  delta prover.round_loop1.body
  all_goals rfl
#print axioms erase_369

/-- Full symbolic source-function equality for `prover.round_loop1`. -/
theorem erase_370 (ops other : ExternalFuns) :
    @prover.round_loop1 _ (replace ops other) = @prover.round_loop1 _ ops := by
  delta prover.round_loop1
  try simp only [erase_369 ops other]
  all_goals rfl
#print axioms erase_370

/-- Full symbolic source-function equality for `prover.round`. -/
theorem erase_371 (ops other : ExternalFuns) :
    @prover.round _ (replace ops other) = @prover.round _ ops := by
  delta prover.round
  try simp only [erase_368 ops other, erase_370 ops other]
  all_goals rfl
#print axioms erase_371

/-- Full symbolic source-function equality for `prover.finish_opening`. -/
theorem erase_372 (ops other : ExternalFuns) :
    @prover.finish_opening _ (replace ops other) = @prover.finish_opening _ ops := by
  delta prover.finish_opening
  try simp only [erase_59 ops other, erase_346 ops other, erase_347 ops other, erase_348 ops other, erase_308 ops other, erase_311 ops other, erase_351 ops other, erase_355 ops other, erase_360 ops other, erase_362 ops other, erase_371 ops other]
  all_goals rfl
#print axioms erase_372

/-- Full symbolic source-function equality for `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact`. -/
theorem erase_373 (ops other : ExternalFuns) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact _ (replace ops other) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact _ ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
  all_goals rfl
#print axioms erase_373

/-- Full symbolic source-function equality for `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq`. -/
theorem erase_374 (ops other : ExternalFuns) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq _ (replace ops other) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq _ ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCmpEq
  try simp only [erase_373 ops other]
  all_goals rfl
#print axioms erase_374

/-- Full symbolic source-function equality for `aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField`. -/
theorem erase_375 (ops other : ExternalFuns) :
    @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField _ (replace ops other) = @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField _ ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
  try simp only [erase_374 ops other, erase_273 ops other]
  all_goals rfl
#print axioms erase_375

/-- Full symbolic source-function equality for `host_transcript.Transcript.new`. -/
theorem erase_376 (ops other : ExternalFuns) :
    @host_transcript.Transcript.new _ (replace ops other) = @host_transcript.Transcript.new _ ops := by
  delta host_transcript.Transcript.new
  all_goals rfl
#print axioms erase_376

/-- Full symbolic source-function equality for `prover.opening_row_loop.body`. -/
theorem erase_377 (ops other : ExternalFuns) :
    @prover.opening_row_loop.body _ (replace ops other) = @prover.opening_row_loop.body _ ops := by
  delta prover.opening_row_loop.body
  all_goals rfl
#print axioms erase_377

/-- Full symbolic source-function equality for `prover.opening_row_loop`. -/
theorem erase_378 (ops other : ExternalFuns) :
    @prover.opening_row_loop _ (replace ops other) = @prover.opening_row_loop _ ops := by
  delta prover.opening_row_loop
  try simp only [erase_377 ops other]
  all_goals rfl
#print axioms erase_378

/-- Full symbolic source-function equality for `prover.opening_row`. -/
theorem erase_379 (ops other : ExternalFuns) :
    @prover.opening_row _ (replace ops other) = @prover.opening_row _ ops := by
  delta prover.opening_row
  try simp only [erase_378 ops other]
  all_goals rfl
#print axioms erase_379

/-- Full symbolic source-function equality for `prover.opening_batch_loop.body`. -/
theorem erase_380 (ops other : ExternalFuns) :
    @prover.opening_batch_loop.body _ (replace ops other) = @prover.opening_batch_loop.body _ ops := by
  delta prover.opening_batch_loop.body
  try simp only [erase_379 ops other]
  all_goals rfl
#print axioms erase_380

/-- Full symbolic source-function equality for `prover.opening_batch_loop`. -/
theorem erase_381 (ops other : ExternalFuns) :
    @prover.opening_batch_loop _ (replace ops other) = @prover.opening_batch_loop _ ops := by
  delta prover.opening_batch_loop
  try simp only [erase_380 ops other]
  all_goals rfl
#print axioms erase_381

/-- Full symbolic source-function equality for `prover.opening_batch`. -/
theorem erase_382 (ops other : ExternalFuns) :
    @prover.opening_batch _ (replace ops other) = @prover.opening_batch _ ops := by
  delta prover.opening_batch
  try simp only [erase_381 ops other]
  all_goals rfl
#print axioms erase_382

/-- Full symbolic source-function equality for `prover.opening_claim_bytes_loop.body`. -/
theorem erase_383 (ops other : ExternalFuns) :
    @prover.opening_claim_bytes_loop.body _ (replace ops other) = @prover.opening_claim_bytes_loop.body _ ops := by
  delta prover.opening_claim_bytes_loop.body
  try simp only [erase_375 ops other]
  all_goals rfl
#print axioms erase_383
end R1Z.PDict_ReachErase
