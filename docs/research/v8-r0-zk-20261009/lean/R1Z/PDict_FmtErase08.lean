import R1Z.PDict_FmtErase07
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `aspis_core.field.M31.Insts.CoreCmpPartialEqM31`. -/
theorem erase_128 (ops other : ExternalFuns) :
    @aspis_core.field.M31.Insts.CoreCmpPartialEqM31 _ (replace ops other) = @aspis_core.field.M31.Insts.CoreCmpPartialEqM31 _ ops := by
  delta aspis_core.field.M31.Insts.CoreCmpPartialEqM31
  all_goals rfl
#print axioms erase_128

/-- Full symbolic source-function equality for `aspis_core.field.M31.Insts.CoreCmpEq`. -/
theorem erase_129 (ops other : ExternalFuns) :
    @aspis_core.field.M31.Insts.CoreCmpEq _ (replace ops other) = @aspis_core.field.M31.Insts.CoreCmpEq _ ops := by
  delta aspis_core.field.M31.Insts.CoreCmpEq
  try simp only [erase_128 ops other]
  all_goals rfl
#print axioms erase_129

/-- Full symbolic source-function equality for `aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField`. -/
theorem erase_130 (ops other : ExternalFuns) :
    @aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField _ (replace ops other) = @aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField _ ops := by
  delta aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField
  try simp only [erase_129 ops other, erase_118 ops other]
  all_goals rfl
#print axioms erase_130

/-- Full symbolic source-function equality for `host_commitment.domain_points_loop.body`. -/
theorem erase_131 (ops other : ExternalFuns) :
    @host_commitment.domain_points_loop.body _ (replace ops other) = @host_commitment.domain_points_loop.body _ ops := by
  delta host_commitment.domain_points_loop.body
  try simp only [erase_130 ops other]
  all_goals rfl
#print axioms erase_131

/-- Full symbolic source-function equality for `host_commitment.domain_points_loop`. -/
theorem erase_132 (ops other : ExternalFuns) :
    @host_commitment.domain_points_loop _ (replace ops other) = @host_commitment.domain_points_loop _ ops := by
  delta host_commitment.domain_points_loop
  try simp only [erase_131 ops other]
  all_goals rfl
#print axioms erase_132

/-- Full symbolic source-function equality for `host_commitment.domain_points`. -/
theorem erase_133 (ops other : ExternalFuns) :
    @host_commitment.domain_points _ (replace ops other) = @host_commitment.domain_points _ ops := by
  delta host_commitment.domain_points
  try simp only [erase_118 ops other, erase_127 ops other, erase_132 ops other]
  all_goals rfl
#print axioms erase_133

/-- Full symbolic source-function equality for `host_commitment.EncodingDomain.new`. -/
theorem erase_134 (ops other : ExternalFuns) :
    @host_commitment.EncodingDomain.new _ (replace ops other) = @host_commitment.EncodingDomain.new _ ops := by
  delta host_commitment.EncodingDomain.new
  try simp only [erase_122 ops other, erase_125 ops other, erase_133 ops other]
  all_goals rfl
#print axioms erase_134

/-- Full symbolic source-function equality for `aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1`. -/
theorem erase_135 (ops other : ExternalFuns) :
    @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1 _ (replace ops other) = @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1 _ ops := by
  delta aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
  all_goals rfl
#print axioms erase_135

/-- Full symbolic source-function equality for `aspis_core.field.QM31.Insts.CoreMarkerCopy`. -/
theorem erase_136 (ops other : ExternalFuns) :
    @aspis_core.field.QM31.Insts.CoreMarkerCopy _ (replace ops other) = @aspis_core.field.QM31.Insts.CoreMarkerCopy _ ops := by
  delta aspis_core.field.QM31.Insts.CoreMarkerCopy
  try simp only [erase_101 ops other]
  all_goals rfl
#print axioms erase_136

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.add_h1_padding_loop.body`. -/
theorem erase_137 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.add_h1_padding_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.add_h1_padding_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.add_h1_padding_loop.body
  all_goals rfl
#print axioms erase_137

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.add_h1_padding_loop`. -/
theorem erase_138 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.add_h1_padding_loop _ (replace ops other) = @aspis_prover.state_only_hiding.add_h1_padding_loop _ ops := by
  delta aspis_prover.state_only_hiding.add_h1_padding_loop
  try simp only [erase_137 ops other]
  all_goals rfl
#print axioms erase_138

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.add_h1_padding`. -/
theorem erase_139 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.add_h1_padding _ (replace ops other) = @aspis_prover.state_only_hiding.add_h1_padding _ ops := by
  delta aspis_prover.state_only_hiding.add_h1_padding
  try simp only [erase_138 ops other]
  all_goals rfl
#print axioms erase_139

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.check_h1_padding_active_loop.body`. -/
theorem erase_140 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.check_h1_padding_active_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.check_h1_padding_active_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.check_h1_padding_active_loop.body
  try simp only [erase_60 ops other]
  all_goals rfl
#print axioms erase_140

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.check_h1_padding_active_loop`. -/
theorem erase_141 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.check_h1_padding_active_loop _ (replace ops other) = @aspis_prover.state_only_hiding.check_h1_padding_active_loop _ ops := by
  delta aspis_prover.state_only_hiding.check_h1_padding_active_loop
  try simp only [erase_140 ops other]
  all_goals rfl
#print axioms erase_141

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.check_h1_padding_active`. -/
theorem erase_142 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.check_h1_padding_active _ (replace ops other) = @aspis_prover.state_only_hiding.check_h1_padding_active _ ops := by
  delta aspis_prover.state_only_hiding.check_h1_padding_active
  try simp only [erase_141 ops other]
  all_goals rfl
#print axioms erase_142

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.h1_padding_inactive_step`. -/
theorem erase_143 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_step _ (replace ops other) = @aspis_prover.state_only_hiding.h1_padding_inactive_step _ ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_step
  all_goals rfl
#print axioms erase_143
end R1Z.PDict_FmtErase
