import R1Z.PDict_PrepareOpening222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_tree.check_indices`. -/
theorem erase_400 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.check_indices (types base F) (selected base F ops) = @host_tree.check_indices base ops := by
  delta host_tree.check_indices
  try simp only [erase_399 base F ops]
  all_goals rfl
#print axioms erase_400

/-- Carrier transport candidate for `host_tree.node_count`. -/
theorem erase_401 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.node_count (types base F) (selected base F ops) = @host_tree.node_count base ops := by
  delta host_tree.node_count
  try simp only [erase_400 base F ops]
  all_goals rfl
#print axioms erase_401

/-- Carrier transport candidate for `host_tree.BinaryTree.multiproof`. -/
theorem erase_402 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.BinaryTree.multiproof (types base F) (selected base F ops) = @host_tree.BinaryTree.multiproof base ops := by
  delta host_tree.BinaryTree.multiproof
  try simp only [erase_397 base F ops, erase_401 base F ops]
  all_goals rfl
#print axioms erase_402

/-- Carrier transport candidate for `host_commitment.Commitment.multiproof`. -/
theorem erase_403 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.multiproof (types base F) (selected base F ops) = @host_commitment.Commitment.multiproof base ops := by
  delta host_commitment.Commitment.multiproof
  try simp only [erase_402 base F ops]
  all_goals rfl
#print axioms erase_403

/-- Carrier transport candidate for `prover.append_node_slot`. -/
theorem erase_404 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_node_slot (types base F) (selected base F ops) = @prover.append_node_slot base ops := by
  delta prover.append_node_slot
  try simp only [erase_403 base F ops, erase_402 base F ops]
  all_goals rfl
#print axioms erase_404

/-- Carrier transport candidate for `prover.append_node_slots`. -/
theorem erase_405 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_node_slots (types base F) (selected base F ops) = @prover.append_node_slots base ops := by
  delta prover.append_node_slots
  try simp only [erase_404 base F ops]
  all_goals rfl
#print axioms erase_405

/-- Carrier transport candidate for `host_commitment.opening_lane_values`. -/
theorem erase_406 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.opening_lane_values (types base F) (selected base F ops) = @host_commitment.opening_lane_values base ops := by
  delta host_commitment.opening_lane_values
  try simp only [erase_260 base F ops]
  all_goals rfl
#print axioms erase_406

/-- Carrier transport candidate for `host_commitment.fill_opening_values`. -/
theorem erase_407 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.fill_opening_values (types base F) (selected base F ops) = @host_commitment.fill_opening_values base ops := by
  funext c u
  delta host_commitment.fill_opening_values
  apply fixed_equal
  funext recur values j
  try simp only [erase_406 base F ops]
  all_goals rfl
#print axioms erase_407

/-- Carrier transport candidate for `host_commitment.Commitment.fill_opening`. -/
theorem erase_408 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.fill_opening (types base F) (selected base F ops) = @host_commitment.Commitment.fill_opening base ops := by
  delta host_commitment.Commitment.fill_opening
  try simp only [erase_407 base F ops]
  all_goals rfl
#print axioms erase_408

/-- Carrier transport candidate for `host_commitment.Commitment.opening_salt`. -/
theorem erase_409 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.opening_salt (types base F) (selected base F ops) = @host_commitment.Commitment.opening_salt base ops := by
  delta host_commitment.Commitment.opening_salt
  all_goals rfl
#print axioms erase_409

/-- Carrier transport candidate for `prover.append_opening_base_row_loop.body`. -/
theorem erase_410 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_base_row_loop.body (types base F) (selected base F ops) = @prover.append_opening_base_row_loop.body base ops := by
  delta prover.append_opening_base_row_loop.body
  all_goals rfl
#print axioms erase_410

/-- Carrier transport candidate for `prover.append_opening_base_row_loop`. -/
theorem erase_411 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_base_row_loop (types base F) (selected base F ops) = @prover.append_opening_base_row_loop base ops := by
  delta prover.append_opening_base_row_loop
  try simp only [erase_410 base F ops]
  all_goals rfl
#print axioms erase_411

/-- Carrier transport candidate for `prover.append_opening_base_row`. -/
theorem erase_412 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_base_row (types base F) (selected base F ops) = @prover.append_opening_base_row base ops := by
  delta prover.append_opening_base_row
  try simp only [erase_411 base F ops]
  all_goals rfl
#print axioms erase_412

/-- Carrier transport candidate for `prover.append_opening_secure_row_loop.body`. -/
theorem erase_413 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_secure_row_loop.body (types base F) (selected base F ops) = @prover.append_opening_secure_row_loop.body base ops := by
  delta prover.append_opening_secure_row_loop.body
  all_goals rfl
#print axioms erase_413

/-- Carrier transport candidate for `prover.append_opening_secure_row_loop`. -/
theorem erase_414 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_secure_row_loop (types base F) (selected base F ops) = @prover.append_opening_secure_row_loop base ops := by
  delta prover.append_opening_secure_row_loop
  try simp only [erase_413 base F ops]
  all_goals rfl
#print axioms erase_414

/-- Carrier transport candidate for `prover.append_opening_secure_row`. -/
theorem erase_415 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_secure_row (types base F) (selected base F ops) = @prover.append_opening_secure_row base ops := by
  delta prover.append_opening_secure_row
  try simp only [erase_414 base F ops]
  all_goals rfl
#print axioms erase_415
end R1Z.PDict_Static222
