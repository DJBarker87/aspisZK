import R1Z.PDict_Static222_16
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_commitment.commitment_leaves`. -/
theorem erase_272 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaves (types base F) (selected base F ops) = @host_commitment.commitment_leaves base ops := by
  delta host_commitment.commitment_leaves
  try simp only [erase_259 base F ops, erase_268 base F ops, erase_271 base F ops]
  all_goals rfl
#print axioms erase_272

/-- Carrier transport candidate for `aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy`. -/
theorem erase_273 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy base ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy
  try simp only [erase_61 base F ops]
  all_goals rfl
#print axioms erase_273

/-- Carrier transport candidate for `host_commitment.merge_evaluations`. -/
theorem erase_274 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.merge_evaluations (types base F) (selected base F ops) = @host_commitment.merge_evaluations base ops := by
  delta host_commitment.merge_evaluations
  all_goals rfl
#print axioms erase_274

/-- Carrier transport candidate for `host_commitment.split_coefficients`. -/
theorem erase_275 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.split_coefficients (types base F) (selected base F ops) = @host_commitment.split_coefficients base ops := by
  delta host_commitment.split_coefficients
  all_goals rfl
#print axioms erase_275

#print host_commitment.EncodingDomain.evaluate
/-- Carrier transport candidate for `host_commitment.EncodingDomain.evaluate`. -/
theorem erase_276 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.EncodingDomain.evaluate (types base F) (selected base F ops) = @host_commitment.EncodingDomain.evaluate base ops := by
  funext T code self
  delta host_commitment.EncodingDomain.evaluate
  apply fixed_equal
  funext recur coefficients depth
  try simp only [erase_274 base F ops, erase_275 base F ops]
  all_goals rfl
#print axioms erase_276

/-- Carrier transport candidate for `host_commitment.EncodingDomain.encode_channel`. -/
theorem erase_277 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.EncodingDomain.encode_channel (types base F) (selected base F ops) = @host_commitment.EncodingDomain.encode_channel base ops := by
  delta host_commitment.EncodingDomain.encode_channel
  try simp only [erase_276 base F ops]
  all_goals rfl
#print axioms erase_277

/-- Carrier transport candidate for `host_commitment.encode_fibre`. -/
theorem erase_278 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_fibre (types base F) (selected base F ops) = @host_commitment.encode_fibre base ops := by
  delta host_commitment.encode_fibre
  all_goals rfl
#print axioms erase_278

/-- Carrier transport candidate for `host_commitment.EncodingDomain.encode_loop.body`. -/
theorem erase_279 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.EncodingDomain.encode_loop.body (types base F) (selected base F ops) = @host_commitment.EncodingDomain.encode_loop.body base ops := by
  delta host_commitment.EncodingDomain.encode_loop.body
  try simp only [erase_278 base F ops]
  all_goals rfl
#print axioms erase_279

/-- Carrier transport candidate for `host_commitment.EncodingDomain.encode_loop`. -/
theorem erase_280 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.EncodingDomain.encode_loop (types base F) (selected base F ops) = @host_commitment.EncodingDomain.encode_loop base ops := by
  delta host_commitment.EncodingDomain.encode_loop
  try simp only [erase_279 base F ops]
  all_goals rfl
#print axioms erase_280

/-- Carrier transport candidate for `host_commitment.EncodingDomain.encode`. -/
theorem erase_281 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.EncodingDomain.encode (types base F) (selected base F ops) = @host_commitment.EncodingDomain.encode base ops := by
  delta host_commitment.EncodingDomain.encode
  try simp only [erase_277 base F ops, erase_280 base F ops]
  all_goals rfl
#print axioms erase_281

/-- Carrier transport candidate for `host_commitment.base_coefficients_loop.body`. -/
theorem erase_282 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.base_coefficients_loop.body (types base F) (selected base F ops) = @host_commitment.base_coefficients_loop.body base ops := by
  delta host_commitment.base_coefficients_loop.body
  all_goals rfl
#print axioms erase_282

/-- Carrier transport candidate for `host_commitment.base_coefficients_loop`. -/
theorem erase_283 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.base_coefficients_loop (types base F) (selected base F ops) = @host_commitment.base_coefficients_loop base ops := by
  delta host_commitment.base_coefficients_loop
  try simp only [erase_282 base F ops]
  all_goals rfl
#print axioms erase_283

/-- Carrier transport candidate for `host_commitment.base_coefficients`. -/
theorem erase_284 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.base_coefficients (types base F) (selected base F ops) = @host_commitment.base_coefficients base ops := by
  delta host_commitment.base_coefficients
  try simp only [erase_283 base F ops]
  all_goals rfl
#print axioms erase_284

/-- Carrier transport candidate for `host_commitment.secure_coefficients_loop.body`. -/
theorem erase_285 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.secure_coefficients_loop.body (types base F) (selected base F ops) = @host_commitment.secure_coefficients_loop.body base ops := by
  delta host_commitment.secure_coefficients_loop.body
  all_goals rfl
#print axioms erase_285

/-- Carrier transport candidate for `host_commitment.secure_coefficients_loop`. -/
theorem erase_286 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.secure_coefficients_loop (types base F) (selected base F ops) = @host_commitment.secure_coefficients_loop base ops := by
  delta host_commitment.secure_coefficients_loop
  try simp only [erase_285 base F ops]
  all_goals rfl
#print axioms erase_286

/-- Carrier transport candidate for `host_commitment.secure_coefficients`. -/
theorem erase_287 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.secure_coefficients (types base F) (selected base F ops) = @host_commitment.secure_coefficients base ops := by
  delta host_commitment.secure_coefficients
  try simp only [erase_286 base F ops]
  all_goals rfl
#print axioms erase_287
/-- Carrier transport candidate for `host_commitment.encode_commitment_lane`. -/
theorem erase_288 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_lane (types base F) (selected base F ops) = @host_commitment.encode_commitment_lane base ops := by
  delta host_commitment.encode_commitment_lane
  try simp only [erase_130 base F ops, erase_175 base F ops, erase_273 base F ops, erase_281 base F ops, erase_284 base F ops, erase_287 base F ops]
  all_goals rfl
#print axioms erase_288

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call`. -/
theorem erase_289 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
  try simp only [erase_288 base F ops]
  all_goals rfl
#print axioms erase_289

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`. -/
theorem erase_290 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
  try simp only [erase_289 base F ops]
  all_goals rfl
#print axioms erase_290

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once`. -/
theorem erase_291 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once
  try simp only [erase_290 base F ops]
  all_goals rfl
#print axioms erase_291

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError`. -/
theorem erase_292 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError
  try simp only [erase_291 base F ops]
  all_goals rfl
#print axioms erase_292

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError`. -/
theorem erase_293 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError
  try simp only [erase_290 base F ops, erase_292 base F ops]
  all_goals rfl
#print axioms erase_293

/-- Carrier transport candidate for `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError`. -/
theorem erase_294 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError (types base F) (selected base F ops) = @host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError base ops := by
  delta host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError
  try simp only [erase_293 base F ops, erase_289 base F ops]
  all_goals rfl
#print axioms erase_294

/-- Carrier transport candidate for `host_commitment.encode_commitment_words_loop1.body`. -/
theorem erase_295 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words_loop1.body (types base F) (selected base F ops) = @host_commitment.encode_commitment_words_loop1.body base ops := by
  delta host_commitment.encode_commitment_words_loop1.body
  all_goals rfl
#print axioms erase_295

/-- Carrier transport candidate for `host_commitment.encode_commitment_words_loop1`. -/
theorem erase_296 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words_loop1 (types base F) (selected base F ops) = @host_commitment.encode_commitment_words_loop1 base ops := by
  delta host_commitment.encode_commitment_words_loop1
  try simp only [erase_295 base F ops]
  all_goals rfl
#print axioms erase_296

/-- Carrier transport candidate for `host_commitment.validate_lane_loop.body`. -/
theorem erase_297 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_lane_loop.body (types base F) (selected base F ops) = @host_commitment.validate_lane_loop.body base ops := by
  delta host_commitment.validate_lane_loop.body
  all_goals rfl
#print axioms erase_297

/-- Carrier transport candidate for `host_commitment.validate_lane_loop`. -/
theorem erase_298 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_lane_loop (types base F) (selected base F ops) = @host_commitment.validate_lane_loop base ops := by
  delta host_commitment.validate_lane_loop
  try simp only [erase_297 base F ops]
  all_goals rfl
#print axioms erase_298

/-- Carrier transport candidate for `host_commitment.validate_lane`. -/
theorem erase_299 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_lane (types base F) (selected base F ops) = @host_commitment.validate_lane base ops := by
  delta host_commitment.validate_lane
  try simp only [erase_298 base F ops]
  all_goals rfl
#print axioms erase_299

/-- Carrier transport candidate for `host_commitment.validate_commitment_lanes_loop.body`. -/
theorem erase_300 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_commitment_lanes_loop.body (types base F) (selected base F ops) = @host_commitment.validate_commitment_lanes_loop.body base ops := by
  delta host_commitment.validate_commitment_lanes_loop.body
  try simp only [erase_299 base F ops]
  all_goals rfl
#print axioms erase_300

/-- Carrier transport candidate for `host_commitment.validate_commitment_lanes_loop`. -/
theorem erase_301 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_commitment_lanes_loop (types base F) (selected base F ops) = @host_commitment.validate_commitment_lanes_loop base ops := by
  delta host_commitment.validate_commitment_lanes_loop
  try simp only [erase_300 base F ops]
  all_goals rfl
#print axioms erase_301

/-- Carrier transport candidate for `host_commitment.validate_commitment_lanes`. -/
theorem erase_302 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.validate_commitment_lanes (types base F) (selected base F ops) = @host_commitment.validate_commitment_lanes base ops := by
  delta host_commitment.validate_commitment_lanes
  try simp only [erase_301 base F ops]
  all_goals rfl
#print axioms erase_302

/-- Carrier transport candidate for `host_commitment.encode_commitment_words`. -/
theorem erase_303 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.encode_commitment_words (types base F) (selected base F ops) = @host_commitment.encode_commitment_words base ops := by
  delta host_commitment.encode_commitment_words
  try simp only [erase_294 base F ops, erase_296 base F ops, erase_302 base F ops]
  all_goals rfl
#print axioms erase_303
end R1Z.PDict_Static222
