import R1Z.PDict_ReachErase17B
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_tree.next_level_loop.body`. -/
theorem erase_304 (ops other : ExternalFuns) :
    @host_tree.next_level_loop.body _ (replace ops other) = @host_tree.next_level_loop.body _ ops := by
  delta host_tree.next_level_loop.body
  all_goals rfl
#print axioms erase_304

/-- Full symbolic source-function equality for `host_tree.next_level_loop`. -/
theorem erase_305 (ops other : ExternalFuns) :
    @host_tree.next_level_loop _ (replace ops other) = @host_tree.next_level_loop _ ops := by
  delta host_tree.next_level_loop
  try simp only [erase_304 ops other]
  all_goals rfl
#print axioms erase_305

/-- Full symbolic source-function equality for `host_tree.next_level`. -/
theorem erase_306 (ops other : ExternalFuns) :
    @host_tree.next_level _ (replace ops other) = @host_tree.next_level _ ops := by
  delta host_tree.next_level
  try simp only [erase_305 ops other]
  all_goals rfl
#print axioms erase_306

/-- Full symbolic source-function equality for `host_tree.append_levels`. -/
theorem erase_307 (ops other : ExternalFuns) :
    @host_tree.append_levels _ (replace ops other) = @host_tree.append_levels _ ops := by
  funext H digest hash
  delta host_tree.append_levels
  apply fixed_equal
  funext recur levels depth
  try simp only [erase_306 ops other]
  all_goals rfl
#print axioms erase_307

/-- Full symbolic source-function equality for `host_tree.BinaryTree.new`. -/
theorem erase_308 (ops other : ExternalFuns) :
    @host_tree.BinaryTree.new _ (replace ops other) = @host_tree.BinaryTree.new _ ops := by
  delta host_tree.BinaryTree.new
  try simp only [erase_307 ops other]
  all_goals rfl
#print axioms erase_308

/-- Full symbolic source-function equality for `host_commitment.Commitment.build`. -/
theorem erase_309 (ops other : ExternalFuns) :
    @host_commitment.Commitment.build _ (replace ops other) = @host_commitment.Commitment.build _ ops := by
  delta host_commitment.Commitment.build
  try simp only [erase_59 ops other, erase_258 ops other, erase_272 ops other, erase_303 ops other, erase_308 ops other]
  all_goals rfl
#print axioms erase_309

/-- Full symbolic source-function equality for `host_commitment.Commitment.new_salted`. -/
theorem erase_310 (ops other : ExternalFuns) :
    @host_commitment.Commitment.new_salted _ (replace ops other) = @host_commitment.Commitment.new_salted _ ops := by
  delta host_commitment.Commitment.new_salted
  try simp only [erase_309 ops other]
  all_goals rfl
#print axioms erase_310

/-- Full symbolic source-function equality for `host_tree.BinaryTree.root`. -/
theorem erase_311 (ops other : ExternalFuns) :
    @host_tree.BinaryTree.root _ (replace ops other) = @host_tree.BinaryTree.root _ ops := by
  delta host_tree.BinaryTree.root
  all_goals rfl
#print axioms erase_311

/-- Full symbolic source-function equality for `host_commitment.Commitment.root`. -/
theorem erase_312 (ops other : ExternalFuns) :
    @host_commitment.Commitment.root _ (replace ops other) = @host_commitment.Commitment.root _ ops := by
  delta host_commitment.Commitment.root
  try simp only [erase_311 ops other]
  all_goals rfl
#print axioms erase_312

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body`. -/
theorem erase_313 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body
  all_goals rfl
#print axioms erase_313

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0`. -/
theorem erase_314 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0
  try simp only [erase_313 ops other]
  all_goals rfl
#print axioms erase_314

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body`. -/
theorem erase_315 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body
  try simp only [erase_314 ops other]
  all_goals rfl
#print axioms erase_315

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0`. -/
theorem erase_316 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
  try simp only [erase_315 ops other]
  all_goals rfl
#print axioms erase_316

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body`. -/
theorem erase_317 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body
  all_goals rfl
#print axioms erase_317

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1`. -/
theorem erase_318 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1
  try simp only [erase_317 ops other]
  all_goals rfl
#print axioms erase_318

/-- Full symbolic source-function equality for `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1`. -/
theorem erase_319 (ops other : ExternalFuns) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 _ (replace ops other) = @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 _ ops := by
  delta prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  try simp only [erase_310 ops other, erase_312 ops other, erase_316 ops other, erase_318 ops other]
  all_goals rfl
#print axioms erase_319
end R1Z.PDict_ReachErase
