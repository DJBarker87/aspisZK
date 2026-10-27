import R1Z.PDict_FmtErase17
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_lane`. -/
theorem erase_288 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_lane _ (replace ops other) = @host_commitment.encode_commitment_lane _ ops := by
  delta host_commitment.encode_commitment_lane
  try simp only [erase_130 ops other, erase_175 ops other, erase_273 ops other, erase_281 ops other, erase_284 ops other, erase_287 ops other]
  all_goals rfl
#print axioms erase_288

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call`. -/
theorem erase_289 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
  try simp only [erase_288 ops other]
  all_goals rfl
#print axioms erase_289

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`. -/
theorem erase_290 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
  try simp only [erase_289 ops other]
  all_goals rfl
#print axioms erase_290

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once`. -/
theorem erase_291 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once
  try simp only [erase_290 ops other]
  all_goals rfl
#print axioms erase_291

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError`. -/
theorem erase_292 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError
  try simp only [erase_291 ops other]
  all_goals rfl
#print axioms erase_292

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError`. -/
theorem erase_293 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError
  try simp only [erase_290 ops other, erase_292 ops other]
  all_goals rfl
#print axioms erase_293

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError`. -/
theorem erase_294 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError _ (replace ops other) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError _ ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError
  try simp only [erase_293 ops other, erase_289 ops other]
  all_goals rfl
#print axioms erase_294

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words_loop1.body`. -/
theorem erase_295 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words_loop1.body _ (replace ops other) = @host_commitment.encode_commitment_words_loop1.body _ ops := by
  delta host_commitment.encode_commitment_words_loop1.body
  all_goals rfl
#print axioms erase_295

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words_loop1`. -/
theorem erase_296 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words_loop1 _ (replace ops other) = @host_commitment.encode_commitment_words_loop1 _ ops := by
  delta host_commitment.encode_commitment_words_loop1
  try simp only [erase_295 ops other]
  all_goals rfl
#print axioms erase_296

/-- Full symbolic source-function equality for `host_commitment.validate_lane_loop.body`. -/
theorem erase_297 (ops other : ExternalFuns) :
    @host_commitment.validate_lane_loop.body _ (replace ops other) = @host_commitment.validate_lane_loop.body _ ops := by
  delta host_commitment.validate_lane_loop.body
  all_goals rfl
#print axioms erase_297

/-- Full symbolic source-function equality for `host_commitment.validate_lane_loop`. -/
theorem erase_298 (ops other : ExternalFuns) :
    @host_commitment.validate_lane_loop _ (replace ops other) = @host_commitment.validate_lane_loop _ ops := by
  delta host_commitment.validate_lane_loop
  try simp only [erase_297 ops other]
  all_goals rfl
#print axioms erase_298

/-- Full symbolic source-function equality for `host_commitment.validate_lane`. -/
theorem erase_299 (ops other : ExternalFuns) :
    @host_commitment.validate_lane _ (replace ops other) = @host_commitment.validate_lane _ ops := by
  delta host_commitment.validate_lane
  try simp only [erase_298 ops other]
  all_goals rfl
#print axioms erase_299

/-- Full symbolic source-function equality for `host_commitment.validate_commitment_lanes_loop.body`. -/
theorem erase_300 (ops other : ExternalFuns) :
    @host_commitment.validate_commitment_lanes_loop.body _ (replace ops other) = @host_commitment.validate_commitment_lanes_loop.body _ ops := by
  delta host_commitment.validate_commitment_lanes_loop.body
  try simp only [erase_299 ops other]
  all_goals rfl
#print axioms erase_300

/-- Full symbolic source-function equality for `host_commitment.validate_commitment_lanes_loop`. -/
theorem erase_301 (ops other : ExternalFuns) :
    @host_commitment.validate_commitment_lanes_loop _ (replace ops other) = @host_commitment.validate_commitment_lanes_loop _ ops := by
  delta host_commitment.validate_commitment_lanes_loop
  try simp only [erase_300 ops other]
  all_goals rfl
#print axioms erase_301

/-- Full symbolic source-function equality for `host_commitment.validate_commitment_lanes`. -/
theorem erase_302 (ops other : ExternalFuns) :
    @host_commitment.validate_commitment_lanes _ (replace ops other) = @host_commitment.validate_commitment_lanes _ ops := by
  delta host_commitment.validate_commitment_lanes
  try simp only [erase_301 ops other]
  all_goals rfl
#print axioms erase_302

/-- Full symbolic source-function equality for `host_commitment.encode_commitment_words`. -/
theorem erase_303 (ops other : ExternalFuns) :
    @host_commitment.encode_commitment_words _ (replace ops other) = @host_commitment.encode_commitment_words _ ops := by
  delta host_commitment.encode_commitment_words
  try simp only [erase_294 ops other, erase_296 ops other, erase_302 ops other]
  all_goals rfl
#print axioms erase_303
end R1Z.PDict_FmtErase
