import R1Z.PDict_Static222_17B
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_tree.next_level_loop.body`. -/
theorem erase_304 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.next_level_loop.body (types base F) (selected base F ops) = @host_tree.next_level_loop.body base ops := by
  delta host_tree.next_level_loop.body
  all_goals rfl
#print axioms erase_304

/-- Carrier transport candidate for `host_tree.next_level_loop`. -/
theorem erase_305 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.next_level_loop (types base F) (selected base F ops) = @host_tree.next_level_loop base ops := by
  delta host_tree.next_level_loop
  try simp only [erase_304 base F ops]
  all_goals rfl
#print axioms erase_305

/-- Carrier transport candidate for `host_tree.next_level`. -/
theorem erase_306 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.next_level (types base F) (selected base F ops) = @host_tree.next_level base ops := by
  delta host_tree.next_level
  try simp only [erase_305 base F ops]
  all_goals rfl
#print axioms erase_306

/-- Carrier transport candidate for `host_tree.append_levels`. -/
theorem erase_307 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.append_levels (types base F) (selected base F ops) = @host_tree.append_levels base ops := by
  funext H digest hash
  delta host_tree.append_levels
  apply fixed_equal
  funext recur levels depth
  try simp only [erase_306 base F ops]
  all_goals rfl
#print axioms erase_307

/-- Carrier transport candidate for `host_tree.BinaryTree.new`. -/
theorem erase_308 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.BinaryTree.new (types base F) (selected base F ops) = @host_tree.BinaryTree.new base ops := by
  delta host_tree.BinaryTree.new
  try simp only [erase_307 base F ops]
  all_goals rfl
#print axioms erase_308

/-- Carrier transport candidate for `host_commitment.Commitment.build`. -/
theorem erase_309 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.build (types base F) (selected base F ops) = @host_commitment.Commitment.build base ops := by
  delta host_commitment.Commitment.build
  try simp only [erase_59 base F ops, erase_258 base F ops, erase_272 base F ops, erase_303 base F ops, erase_308 base F ops]
  all_goals rfl
#print axioms erase_309

/-- Carrier transport candidate for `host_commitment.Commitment.new_salted`. -/
theorem erase_310 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.new_salted (types base F) (selected base F ops) = @host_commitment.Commitment.new_salted base ops := by
  delta host_commitment.Commitment.new_salted
  try simp only [erase_309 base F ops]
  all_goals rfl
#print axioms erase_310

/-- Carrier transport candidate for `host_tree.BinaryTree.root`. -/
theorem erase_311 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_tree.BinaryTree.root (types base F) (selected base F ops) = @host_tree.BinaryTree.root base ops := by
  delta host_tree.BinaryTree.root
  all_goals rfl
#print axioms erase_311

/-- Carrier transport candidate for `host_commitment.Commitment.root`. -/
theorem erase_312 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.Commitment.root (types base F) (selected base F ops) = @host_commitment.Commitment.root base ops := by
  delta host_commitment.Commitment.root
  try simp only [erase_311 base F ops]
  all_goals rfl
#print axioms erase_312

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body`. -/
theorem erase_313 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body
  all_goals rfl
#print axioms erase_313

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0`. -/
theorem erase_314 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0
  try simp only [erase_313 base F ops]
  all_goals rfl
#print axioms erase_314

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body`. -/
theorem erase_315 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body
  try simp only [erase_314 base F ops]
  all_goals rfl
#print axioms erase_315

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0`. -/
theorem erase_316 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
  try simp only [erase_315 base F ops]
  all_goals rfl
#print axioms erase_316

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body`. -/
theorem erase_317 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body
  all_goals rfl
#print axioms erase_317

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1`. -/
theorem erase_318 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1
  try simp only [erase_317 base F ops]
  all_goals rfl
#print axioms erase_318

/-- Carrier transport candidate for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1`. -/
theorem erase_319 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 (types base F) (selected base F ops) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 base ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  try simp only [erase_310 base F ops, erase_312 base F ops, erase_316 base F ops, erase_318 base F ops]
  all_goals rfl
#print axioms erase_319
end R1Z.PDict_Static222
