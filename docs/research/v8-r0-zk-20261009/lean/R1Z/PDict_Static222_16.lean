import R1Z.PDict_BuildMaterial222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_commitment.commitment_lanes`. -/
theorem erase_258 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_lanes (types base F) (selected base F ops) = @host_commitment.commitment_lanes base ops := by
  delta host_commitment.commitment_lanes
  all_goals rfl
#print axioms erase_258

/-- Carrier transport candidate for `host_commitment.commitment_tag`. -/
theorem erase_259 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_tag (types base F) (selected base F ops) = @host_commitment.commitment_tag base ops := by
  delta host_commitment.commitment_tag
  all_goals rfl
#print axioms erase_259

/-- Carrier transport candidate for `host_commitment.Word.value`. -/
theorem erase_260 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Word.value (types base F) (selected base F ops) = @host_commitment.Word.value base ops := by
  delta host_commitment.Word.value
  all_goals rfl
#print axioms erase_260

/-- Carrier transport candidate for `host_commitment.commitment_leaf_bytes_loop0_loop0.body`. -/
theorem erase_261 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaf_bytes_loop0_loop0.body (types base F) (selected base F ops) = @host_commitment.commitment_leaf_bytes_loop0_loop0.body base ops := by
  delta host_commitment.commitment_leaf_bytes_loop0_loop0.body
  try simp only [erase_260 base F ops]
  all_goals rfl
#print axioms erase_261

/-- Carrier transport candidate for `host_commitment.commitment_leaf_bytes_loop0_loop0`. -/
theorem erase_262 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaf_bytes_loop0_loop0 (types base F) (selected base F ops) = @host_commitment.commitment_leaf_bytes_loop0_loop0 base ops := by
  delta host_commitment.commitment_leaf_bytes_loop0_loop0
  try simp only [erase_261 base F ops]
  all_goals rfl
#print axioms erase_262

/-- Carrier transport candidate for `host_commitment.commitment_leaf_bytes_loop0.body`. -/
theorem erase_263 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaf_bytes_loop0.body (types base F) (selected base F ops) = @host_commitment.commitment_leaf_bytes_loop0.body base ops := by
  delta host_commitment.commitment_leaf_bytes_loop0.body
  try simp only [erase_262 base F ops]
  all_goals rfl
#print axioms erase_263

/-- Carrier transport candidate for `host_commitment.commitment_leaf_bytes_loop0`. -/
theorem erase_264 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaf_bytes_loop0 (types base F) (selected base F ops) = @host_commitment.commitment_leaf_bytes_loop0 base ops := by
  delta host_commitment.commitment_leaf_bytes_loop0
  try simp only [erase_263 base F ops]
  all_goals rfl
#print axioms erase_264

/-- Carrier transport candidate for `host_commitment.commitment_leaf_bytes`. -/
theorem erase_265 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.commitment_leaf_bytes (types base F) (selected base F ops) = @host_commitment.commitment_leaf_bytes base ops := by
  delta host_commitment.commitment_leaf_bytes
  try simp only [erase_264 base F ops]
  all_goals rfl
#print axioms erase_265

/-- Carrier transport candidate for `host_commitment.plain_commitment_leaves_loop.body`. -/
theorem erase_266 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.plain_commitment_leaves_loop.body (types base F) (selected base F ops) = @host_commitment.plain_commitment_leaves_loop.body base ops := by
  delta host_commitment.plain_commitment_leaves_loop.body
  try simp only [erase_265 base F ops]
  all_goals rfl
#print axioms erase_266

/-- Carrier transport candidate for `host_commitment.plain_commitment_leaves_loop`. -/
theorem erase_267 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.plain_commitment_leaves_loop (types base F) (selected base F ops) = @host_commitment.plain_commitment_leaves_loop base ops := by
  delta host_commitment.plain_commitment_leaves_loop
  try simp only [erase_266 base F ops]
  all_goals rfl
#print axioms erase_267

/-- Carrier transport candidate for `host_commitment.plain_commitment_leaves`. -/
theorem erase_268 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.plain_commitment_leaves (types base F) (selected base F ops) = @host_commitment.plain_commitment_leaves base ops := by
  delta host_commitment.plain_commitment_leaves
  try simp only [erase_267 base F ops]
  all_goals rfl
#print axioms erase_268

/-- Carrier transport candidate for `host_commitment.salted_commitment_leaves_loop.body`. -/
theorem erase_269 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.salted_commitment_leaves_loop.body (types base F) (selected base F ops) = @host_commitment.salted_commitment_leaves_loop.body base ops := by
  delta host_commitment.salted_commitment_leaves_loop.body
  try simp only [erase_265 base F ops]
  all_goals rfl
#print axioms erase_269

/-- Carrier transport candidate for `host_commitment.salted_commitment_leaves_loop`. -/
theorem erase_270 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.salted_commitment_leaves_loop (types base F) (selected base F ops) = @host_commitment.salted_commitment_leaves_loop base ops := by
  delta host_commitment.salted_commitment_leaves_loop
  try simp only [erase_269 base F ops]
  all_goals rfl
#print axioms erase_270

/-- Carrier transport candidate for `host_commitment.salted_commitment_leaves`. -/
theorem erase_271 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.salted_commitment_leaves (types base F) (selected base F ops) = @host_commitment.salted_commitment_leaves base ops := by
  delta host_commitment.salted_commitment_leaves
  try simp only [erase_270 base F ops]
  all_goals rfl
#print axioms erase_271
end R1Z.PDict_Static222
