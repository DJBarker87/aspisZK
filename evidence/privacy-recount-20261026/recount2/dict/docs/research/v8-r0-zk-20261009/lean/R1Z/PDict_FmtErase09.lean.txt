import R1Z.PDict_FmtErase08
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body`. -/
theorem erase_144 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body
  try simp only [erase_143 ops other]
  all_goals rfl
#print axioms erase_144

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop`. -/
theorem erase_145 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop _ (replace ops other) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop _ ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop
  try simp only [erase_144 ops other]
  all_goals rfl
#print axioms erase_145

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.h1_padding_inactive_sum`. -/
theorem erase_146 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum _ (replace ops other) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum _ ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum
  try simp only [erase_145 ops other]
  all_goals rfl
#print axioms erase_146

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active`. -/
theorem erase_147 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active _ (replace ops other) = @aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active _ ops := by
  delta aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active
  try simp only [erase_60 ops other, erase_139 ops other, erase_142 ops other, erase_146 ops other]
  all_goals rfl
#print axioms erase_147

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1`. -/
theorem erase_148 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 _ (replace ops other) = @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 _ ops := by
  delta aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
  try simp only [erase_147 ops other, erase_106 ops other]
  all_goals rfl
#print axioms erase_148

/-- Full symbolic source-function equality for `core.option.Option.Insts.CoreCmpPartialEqOption`. -/
theorem erase_149 (ops other : ExternalFuns) :
    @core.option.Option.Insts.CoreCmpPartialEqOption _ (replace ops other) = @core.option.Option.Insts.CoreCmpPartialEqOption _ ops := by
  delta core.option.Option.Insts.CoreCmpPartialEqOption
  all_goals rfl
#print axioms erase_149

/-- Full symbolic source-function equality for `host_semantic.claim_mask_value`. -/
theorem erase_150 (ops other : ExternalFuns) :
    @host_semantic.claim_mask_value _ (replace ops other) = @host_semantic.claim_mask_value _ ops := by
  delta host_semantic.claim_mask_value
  try simp only [erase_136 ops other]
  all_goals rfl
#print axioms erase_150

/-- Full symbolic source-function equality for `host_semantic.extra_loop0_loop0.body`. -/
theorem erase_151 (ops other : ExternalFuns) :
    @host_semantic.extra_loop0_loop0.body _ (replace ops other) = @host_semantic.extra_loop0_loop0.body _ ops := by
  delta host_semantic.extra_loop0_loop0.body
  all_goals rfl
#print axioms erase_151

/-- Full symbolic source-function equality for `host_semantic.extra_loop0_loop0`. -/
theorem erase_152 (ops other : ExternalFuns) :
    @host_semantic.extra_loop0_loop0 _ (replace ops other) = @host_semantic.extra_loop0_loop0 _ ops := by
  delta host_semantic.extra_loop0_loop0
  try simp only [erase_151 ops other]
  all_goals rfl
#print axioms erase_152

/-- Full symbolic source-function equality for `host_semantic.extra_loop0.body`. -/
theorem erase_153 (ops other : ExternalFuns) :
    @host_semantic.extra_loop0.body _ (replace ops other) = @host_semantic.extra_loop0.body _ ops := by
  delta host_semantic.extra_loop0.body
  try simp only [erase_152 ops other]
  all_goals rfl
#print axioms erase_153

/-- Full symbolic source-function equality for `host_semantic.extra_loop0`. -/
theorem erase_154 (ops other : ExternalFuns) :
    @host_semantic.extra_loop0 _ (replace ops other) = @host_semantic.extra_loop0 _ ops := by
  delta host_semantic.extra_loop0
  try simp only [erase_153 ops other]
  all_goals rfl
#print axioms erase_154

/-- Full symbolic source-function equality for `host_semantic.extra`. -/
theorem erase_155 (ops other : ExternalFuns) :
    @host_semantic.extra _ (replace ops other) = @host_semantic.extra _ ops := by
  delta host_semantic.extra
  try simp only [erase_154 ops other]
  all_goals rfl
#print axioms erase_155

/-- Full symbolic source-function equality for `host_semantic.claims_at_point_loop.body`. -/
theorem erase_156 (ops other : ExternalFuns) :
    @host_semantic.claims_at_point_loop.body _ (replace ops other) = @host_semantic.claims_at_point_loop.body _ ops := by
  delta host_semantic.claims_at_point_loop.body
  all_goals rfl
#print axioms erase_156

/-- Full symbolic source-function equality for `host_semantic.claims_at_point_loop`. -/
theorem erase_157 (ops other : ExternalFuns) :
    @host_semantic.claims_at_point_loop _ (replace ops other) = @host_semantic.claims_at_point_loop _ ops := by
  delta host_semantic.claims_at_point_loop
  try simp only [erase_156 ops other]
  all_goals rfl
#print axioms erase_157

/-- Full symbolic source-function equality for `host_semantic.claims_at_point`. -/
theorem erase_158 (ops other : ExternalFuns) :
    @host_semantic.claims_at_point _ (replace ops other) = @host_semantic.claims_at_point _ ops := by
  delta host_semantic.claims_at_point
  try simp only [erase_157 ops other]
  all_goals rfl
#print axioms erase_158

/-- Full symbolic source-function equality for `r1_wire.statement_points`. -/
theorem erase_159 (ops other : ExternalFuns) :
    @r1_wire.statement_points _ (replace ops other) = @r1_wire.statement_points _ ops := by
  delta r1_wire.statement_points
  all_goals rfl
#print axioms erase_159
end R1Z.PDict_FmtErase
