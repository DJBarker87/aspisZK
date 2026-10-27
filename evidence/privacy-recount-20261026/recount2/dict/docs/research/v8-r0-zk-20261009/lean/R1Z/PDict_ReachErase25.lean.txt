import R1Z.PDict_ReachErase24
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_tree.check_indices`. -/
theorem erase_400 (ops other : ExternalFuns) :
    @host_tree.check_indices _ (replace ops other) = @host_tree.check_indices _ ops := by
  delta host_tree.check_indices
  try simp only [erase_399 ops other]
  all_goals rfl
#print axioms erase_400

/-- Full symbolic source-function equality for `host_tree.node_count`. -/
theorem erase_401 (ops other : ExternalFuns) :
    @host_tree.node_count _ (replace ops other) = @host_tree.node_count _ ops := by
  delta host_tree.node_count
  try simp only [erase_400 ops other]
  all_goals rfl
#print axioms erase_401

/-- Full symbolic source-function equality for `host_tree.BinaryTree.multiproof`. -/
theorem erase_402 (ops other : ExternalFuns) :
    @host_tree.BinaryTree.multiproof _ (replace ops other) = @host_tree.BinaryTree.multiproof _ ops := by
  delta host_tree.BinaryTree.multiproof
  try simp only [erase_397 ops other, erase_401 ops other]
  all_goals rfl
#print axioms erase_402

/-- Full symbolic source-function equality for `host_commitment.Commitment.multiproof`. -/
theorem erase_403 (ops other : ExternalFuns) :
    @host_commitment.Commitment.multiproof _ (replace ops other) = @host_commitment.Commitment.multiproof _ ops := by
  delta host_commitment.Commitment.multiproof
  try simp only [erase_402 ops other]
  all_goals rfl
#print axioms erase_403

/-- Full symbolic source-function equality for `prover.append_node_slot`. -/
theorem erase_404 (ops other : ExternalFuns) :
    @prover.append_node_slot _ (replace ops other) = @prover.append_node_slot _ ops := by
  delta prover.append_node_slot
  try simp only [erase_403 ops other, erase_402 ops other]
  all_goals rfl
#print axioms erase_404

/-- Full symbolic source-function equality for `prover.append_node_slots`. -/
theorem erase_405 (ops other : ExternalFuns) :
    @prover.append_node_slots _ (replace ops other) = @prover.append_node_slots _ ops := by
  delta prover.append_node_slots
  try simp only [erase_404 ops other]
  all_goals rfl
#print axioms erase_405

/-- Full symbolic source-function equality for `host_commitment.opening_lane_values`. -/
theorem erase_406 (ops other : ExternalFuns) :
    @host_commitment.opening_lane_values _ (replace ops other) = @host_commitment.opening_lane_values _ ops := by
  delta host_commitment.opening_lane_values
  try simp only [erase_260 ops other]
  all_goals rfl
#print axioms erase_406

/-- Full symbolic source-function equality for `host_commitment.fill_opening_values`. -/
theorem erase_407 (ops other : ExternalFuns) :
    @host_commitment.fill_opening_values _ (replace ops other) = @host_commitment.fill_opening_values _ ops := by
  funext c u
  delta host_commitment.fill_opening_values
  apply fixed_equal
  funext recur values j
  try simp only [erase_406 ops other]
  all_goals rfl
#print axioms erase_407

/-- Full symbolic source-function equality for `host_commitment.Commitment.fill_opening`. -/
theorem erase_408 (ops other : ExternalFuns) :
    @host_commitment.Commitment.fill_opening _ (replace ops other) = @host_commitment.Commitment.fill_opening _ ops := by
  delta host_commitment.Commitment.fill_opening
  try simp only [erase_407 ops other]
  all_goals rfl
#print axioms erase_408

/-- Full symbolic source-function equality for `host_commitment.Commitment.opening_salt`. -/
theorem erase_409 (ops other : ExternalFuns) :
    @host_commitment.Commitment.opening_salt _ (replace ops other) = @host_commitment.Commitment.opening_salt _ ops := by
  delta host_commitment.Commitment.opening_salt
  all_goals rfl
#print axioms erase_409

/-- Full symbolic source-function equality for `prover.append_opening_base_row_loop.body`. -/
theorem erase_410 (ops other : ExternalFuns) :
    @prover.append_opening_base_row_loop.body _ (replace ops other) = @prover.append_opening_base_row_loop.body _ ops := by
  delta prover.append_opening_base_row_loop.body
  all_goals rfl
#print axioms erase_410

/-- Full symbolic source-function equality for `prover.append_opening_base_row_loop`. -/
theorem erase_411 (ops other : ExternalFuns) :
    @prover.append_opening_base_row_loop _ (replace ops other) = @prover.append_opening_base_row_loop _ ops := by
  delta prover.append_opening_base_row_loop
  try simp only [erase_410 ops other]
  all_goals rfl
#print axioms erase_411

/-- Full symbolic source-function equality for `prover.append_opening_base_row`. -/
theorem erase_412 (ops other : ExternalFuns) :
    @prover.append_opening_base_row _ (replace ops other) = @prover.append_opening_base_row _ ops := by
  delta prover.append_opening_base_row
  try simp only [erase_411 ops other]
  all_goals rfl
#print axioms erase_412

/-- Full symbolic source-function equality for `prover.append_opening_secure_row_loop.body`. -/
theorem erase_413 (ops other : ExternalFuns) :
    @prover.append_opening_secure_row_loop.body _ (replace ops other) = @prover.append_opening_secure_row_loop.body _ ops := by
  delta prover.append_opening_secure_row_loop.body
  all_goals rfl
#print axioms erase_413

/-- Full symbolic source-function equality for `prover.append_opening_secure_row_loop`. -/
theorem erase_414 (ops other : ExternalFuns) :
    @prover.append_opening_secure_row_loop _ (replace ops other) = @prover.append_opening_secure_row_loop _ ops := by
  delta prover.append_opening_secure_row_loop
  try simp only [erase_413 ops other]
  all_goals rfl
#print axioms erase_414

/-- Full symbolic source-function equality for `prover.append_opening_secure_row`. -/
theorem erase_415 (ops other : ExternalFuns) :
    @prover.append_opening_secure_row _ (replace ops other) = @prover.append_opening_secure_row _ ops := by
  delta prover.append_opening_secure_row
  try simp only [erase_414 ops other]
  all_goals rfl
#print axioms erase_415
end R1Z.PDict_ReachErase
