import R1Z.PDict_ReachErase16
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_commitment.commitment_leaves`. -/
theorem erase_272 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaves _ (replace ops other) = @host_commitment.commitment_leaves _ ops := by
  delta host_commitment.commitment_leaves
  try simp only [erase_259 ops other, erase_268 ops other, erase_271 ops other]
  all_goals rfl
#print axioms erase_272

/-- Full symbolic source-function equality for `aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy`. -/
theorem erase_273 (ops other : ExternalFuns) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy _ (replace ops other) = @aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy _ ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy
  try simp only [erase_61 ops other]
  all_goals rfl
#print axioms erase_273

/-- Full symbolic source-function equality for `host_commitment.merge_evaluations`. -/
theorem erase_274 (ops other : ExternalFuns) :
    @host_commitment.merge_evaluations _ (replace ops other) = @host_commitment.merge_evaluations _ ops := by
  delta host_commitment.merge_evaluations
  all_goals rfl
#print axioms erase_274

/-- Full symbolic source-function equality for `host_commitment.split_coefficients`. -/
theorem erase_275 (ops other : ExternalFuns) :
    @host_commitment.split_coefficients _ (replace ops other) = @host_commitment.split_coefficients _ ops := by
  delta host_commitment.split_coefficients
  all_goals rfl
#print axioms erase_275

#print host_commitment.EncodingDomain.evaluate
/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.evaluate`. -/
theorem erase_276 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.evaluate _ (replace ops other) = @host_commitment.EncodingDomain.evaluate _ ops := by
  funext T code self
  delta host_commitment.EncodingDomain.evaluate
  apply fixed_equal
  funext recur coefficients depth
  try simp only [erase_274 ops other, erase_275 ops other]
  all_goals rfl
#print axioms erase_276

/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.encode_channel`. -/
theorem erase_277 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.encode_channel _ (replace ops other) = @host_commitment.EncodingDomain.encode_channel _ ops := by
  delta host_commitment.EncodingDomain.encode_channel
  try simp only [erase_276 ops other]
  all_goals rfl
#print axioms erase_277

/-- Full symbolic source-function equality for `host_commitment.encode_fibre`. -/
theorem erase_278 (ops other : ExternalFuns) :
    @host_commitment.encode_fibre _ (replace ops other) = @host_commitment.encode_fibre _ ops := by
  delta host_commitment.encode_fibre
  all_goals rfl
#print axioms erase_278

/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.encode_loop.body`. -/
theorem erase_279 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.encode_loop.body _ (replace ops other) = @host_commitment.EncodingDomain.encode_loop.body _ ops := by
  delta host_commitment.EncodingDomain.encode_loop.body
  try simp only [erase_278 ops other]
  all_goals rfl
#print axioms erase_279

/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.encode_loop`. -/
theorem erase_280 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.encode_loop _ (replace ops other) = @host_commitment.EncodingDomain.encode_loop _ ops := by
  delta host_commitment.EncodingDomain.encode_loop
  try simp only [erase_279 ops other]
  all_goals rfl
#print axioms erase_280

/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.encode`. -/
theorem erase_281 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.encode _ (replace ops other) = @host_commitment.EncodingDomain.encode _ ops := by
  delta host_commitment.EncodingDomain.encode
  try simp only [erase_277 ops other, erase_280 ops other]
  all_goals rfl
#print axioms erase_281

/-- Full symbolic source-function equality for `host_commitment.base_coefficients_loop.body`. -/
theorem erase_282 (ops other : ExternalFuns) :
    @host_commitment.base_coefficients_loop.body _ (replace ops other) = @host_commitment.base_coefficients_loop.body _ ops := by
  delta host_commitment.base_coefficients_loop.body
  all_goals rfl
#print axioms erase_282

/-- Full symbolic source-function equality for `host_commitment.base_coefficients_loop`. -/
theorem erase_283 (ops other : ExternalFuns) :
    @host_commitment.base_coefficients_loop _ (replace ops other) = @host_commitment.base_coefficients_loop _ ops := by
  delta host_commitment.base_coefficients_loop
  try simp only [erase_282 ops other]
  all_goals rfl
#print axioms erase_283

/-- Full symbolic source-function equality for `host_commitment.base_coefficients`. -/
theorem erase_284 (ops other : ExternalFuns) :
    @host_commitment.base_coefficients _ (replace ops other) = @host_commitment.base_coefficients _ ops := by
  delta host_commitment.base_coefficients
  try simp only [erase_283 ops other]
  all_goals rfl
#print axioms erase_284

/-- Full symbolic source-function equality for `host_commitment.secure_coefficients_loop.body`. -/
theorem erase_285 (ops other : ExternalFuns) :
    @host_commitment.secure_coefficients_loop.body _ (replace ops other) = @host_commitment.secure_coefficients_loop.body _ ops := by
  delta host_commitment.secure_coefficients_loop.body
  all_goals rfl
#print axioms erase_285

/-- Full symbolic source-function equality for `host_commitment.secure_coefficients_loop`. -/
theorem erase_286 (ops other : ExternalFuns) :
    @host_commitment.secure_coefficients_loop _ (replace ops other) = @host_commitment.secure_coefficients_loop _ ops := by
  delta host_commitment.secure_coefficients_loop
  try simp only [erase_285 ops other]
  all_goals rfl
#print axioms erase_286

/-- Full symbolic source-function equality for `host_commitment.secure_coefficients`. -/
theorem erase_287 (ops other : ExternalFuns) :
    @host_commitment.secure_coefficients _ (replace ops other) = @host_commitment.secure_coefficients _ ops := by
  delta host_commitment.secure_coefficients
  try simp only [erase_286 ops other]
  all_goals rfl
#print axioms erase_287
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
end R1Z.PDict_ReachErase
