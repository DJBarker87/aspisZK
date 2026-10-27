import R1Z.PDict_FmtErase15
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_semantic.clone_semantic_columns`. -/
theorem erase_256 (ops other : ExternalFuns) :
    @host_semantic.clone_semantic_columns _ (replace ops other) = @host_semantic.clone_semantic_columns _ ops := by
  delta host_semantic.clone_semantic_columns
  try simp only [erase_63 ops other, erase_253 ops other, erase_255 ops other]
  all_goals rfl
#print axioms erase_256

/-- Full symbolic source-function equality for `host_semantic.build_with_material`. -/
theorem erase_257 (ops other : ExternalFuns) :
    @host_semantic.build_with_material _ (replace ops other) = @host_semantic.build_with_material _ ops := by
  delta host_semantic.build_with_material
  try simp only [erase_135 ops other, erase_241 ops other, erase_251 ops other, erase_256 ops other]
  all_goals rfl
#print axioms erase_257

/-- Full symbolic source-function equality for `host_commitment.commitment_lanes`. -/
theorem erase_258 (ops other : ExternalFuns) :
    @host_commitment.commitment_lanes _ (replace ops other) = @host_commitment.commitment_lanes _ ops := by
  delta host_commitment.commitment_lanes
  all_goals rfl
#print axioms erase_258

/-- Full symbolic source-function equality for `host_commitment.commitment_tag`. -/
theorem erase_259 (ops other : ExternalFuns) :
    @host_commitment.commitment_tag _ (replace ops other) = @host_commitment.commitment_tag _ ops := by
  delta host_commitment.commitment_tag
  all_goals rfl
#print axioms erase_259

/-- Full symbolic source-function equality for `host_commitment.Word.value`. -/
theorem erase_260 (ops other : ExternalFuns) :
    @host_commitment.Word.value _ (replace ops other) = @host_commitment.Word.value _ ops := by
  delta host_commitment.Word.value
  all_goals rfl
#print axioms erase_260

/-- Full symbolic source-function equality for `host_commitment.commitment_leaf_bytes_loop0_loop0.body`. -/
theorem erase_261 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaf_bytes_loop0_loop0.body _ (replace ops other) = @host_commitment.commitment_leaf_bytes_loop0_loop0.body _ ops := by
  delta host_commitment.commitment_leaf_bytes_loop0_loop0.body
  try simp only [erase_260 ops other]
  all_goals rfl
#print axioms erase_261

/-- Full symbolic source-function equality for `host_commitment.commitment_leaf_bytes_loop0_loop0`. -/
theorem erase_262 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaf_bytes_loop0_loop0 _ (replace ops other) = @host_commitment.commitment_leaf_bytes_loop0_loop0 _ ops := by
  delta host_commitment.commitment_leaf_bytes_loop0_loop0
  try simp only [erase_261 ops other]
  all_goals rfl
#print axioms erase_262

/-- Full symbolic source-function equality for `host_commitment.commitment_leaf_bytes_loop0.body`. -/
theorem erase_263 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaf_bytes_loop0.body _ (replace ops other) = @host_commitment.commitment_leaf_bytes_loop0.body _ ops := by
  delta host_commitment.commitment_leaf_bytes_loop0.body
  try simp only [erase_262 ops other]
  all_goals rfl
#print axioms erase_263

/-- Full symbolic source-function equality for `host_commitment.commitment_leaf_bytes_loop0`. -/
theorem erase_264 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaf_bytes_loop0 _ (replace ops other) = @host_commitment.commitment_leaf_bytes_loop0 _ ops := by
  delta host_commitment.commitment_leaf_bytes_loop0
  try simp only [erase_263 ops other]
  all_goals rfl
#print axioms erase_264

/-- Full symbolic source-function equality for `host_commitment.commitment_leaf_bytes`. -/
theorem erase_265 (ops other : ExternalFuns) :
    @host_commitment.commitment_leaf_bytes _ (replace ops other) = @host_commitment.commitment_leaf_bytes _ ops := by
  delta host_commitment.commitment_leaf_bytes
  try simp only [erase_264 ops other]
  all_goals rfl
#print axioms erase_265

/-- Full symbolic source-function equality for `host_commitment.plain_commitment_leaves_loop.body`. -/
theorem erase_266 (ops other : ExternalFuns) :
    @host_commitment.plain_commitment_leaves_loop.body _ (replace ops other) = @host_commitment.plain_commitment_leaves_loop.body _ ops := by
  delta host_commitment.plain_commitment_leaves_loop.body
  try simp only [erase_265 ops other]
  all_goals rfl
#print axioms erase_266

/-- Full symbolic source-function equality for `host_commitment.plain_commitment_leaves_loop`. -/
theorem erase_267 (ops other : ExternalFuns) :
    @host_commitment.plain_commitment_leaves_loop _ (replace ops other) = @host_commitment.plain_commitment_leaves_loop _ ops := by
  delta host_commitment.plain_commitment_leaves_loop
  try simp only [erase_266 ops other]
  all_goals rfl
#print axioms erase_267

/-- Full symbolic source-function equality for `host_commitment.plain_commitment_leaves`. -/
theorem erase_268 (ops other : ExternalFuns) :
    @host_commitment.plain_commitment_leaves _ (replace ops other) = @host_commitment.plain_commitment_leaves _ ops := by
  delta host_commitment.plain_commitment_leaves
  try simp only [erase_267 ops other]
  all_goals rfl
#print axioms erase_268

/-- Full symbolic source-function equality for `host_commitment.salted_commitment_leaves_loop.body`. -/
theorem erase_269 (ops other : ExternalFuns) :
    @host_commitment.salted_commitment_leaves_loop.body _ (replace ops other) = @host_commitment.salted_commitment_leaves_loop.body _ ops := by
  delta host_commitment.salted_commitment_leaves_loop.body
  try simp only [erase_265 ops other]
  all_goals rfl
#print axioms erase_269

/-- Full symbolic source-function equality for `host_commitment.salted_commitment_leaves_loop`. -/
theorem erase_270 (ops other : ExternalFuns) :
    @host_commitment.salted_commitment_leaves_loop _ (replace ops other) = @host_commitment.salted_commitment_leaves_loop _ ops := by
  delta host_commitment.salted_commitment_leaves_loop
  try simp only [erase_269 ops other]
  all_goals rfl
#print axioms erase_270

/-- Full symbolic source-function equality for `host_commitment.salted_commitment_leaves`. -/
theorem erase_271 (ops other : ExternalFuns) :
    @host_commitment.salted_commitment_leaves _ (replace ops other) = @host_commitment.salted_commitment_leaves _ ops := by
  delta host_commitment.salted_commitment_leaves
  try simp only [erase_270 ops other]
  all_goals rfl
#print axioms erase_271
end R1Z.PDict_FmtErase
