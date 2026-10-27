import R1Z.PDict_ReachErase09
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_semantic.point_claims`. -/
theorem erase_160 (ops other : ExternalFuns) :
    @host_semantic.point_claims _ (replace ops other) = @host_semantic.point_claims _ ops := by
  delta host_semantic.point_claims
  try simp only [erase_158 ops other, erase_159 ops other]
  all_goals rfl
#print axioms erase_160

/-- Full symbolic source-function equality for `host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate`. -/
theorem erase_161 (ops other : ExternalFuns) :
    @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate _ (replace ops other) = @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate _ ops := by
  delta host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
  try simp only [erase_150 ops other, erase_155 ops other, erase_160 ops other]
  all_goals rfl
#print axioms erase_161

/-- Full symbolic source-function equality for `host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle`. -/
theorem erase_162 (ops other : ExternalFuns) :
    @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle _ (replace ops other) = @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle _ ops := by
  delta host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
  try simp only [erase_161 ops other]
  all_goals rfl
#print axioms erase_162

/-- Full symbolic source-function equality for `host_semantic.d_tail_sum`. -/
theorem erase_163 (ops other : ExternalFuns) :
    @host_semantic.d_tail_sum _ (replace ops other) = @host_semantic.d_tail_sum _ ops := by
  delta host_semantic.d_tail_sum
  all_goals rfl
#print axioms erase_163

/-- Full symbolic source-function equality for `host_semantic.d_tail_side`. -/
theorem erase_164 (ops other : ExternalFuns) :
    @host_semantic.d_tail_side _ (replace ops other) = @host_semantic.d_tail_side _ ops := by
  delta host_semantic.d_tail_side
  try simp only [erase_163 ops other]
  all_goals rfl
#print axioms erase_164

/-- Full symbolic source-function equality for `host_semantic.add_d_tail`. -/
theorem erase_165 (ops other : ExternalFuns) :
    @host_semantic.add_d_tail _ (replace ops other) = @host_semantic.add_d_tail _ ops := by
  delta host_semantic.add_d_tail
  try simp only [erase_164 ops other]
  all_goals rfl
#print axioms erase_165

/-- Full symbolic source-function equality for `host_semantic.check_secure_column_loop.body`. -/
theorem erase_166 (ops other : ExternalFuns) :
    @host_semantic.check_secure_column_loop.body _ (replace ops other) = @host_semantic.check_secure_column_loop.body _ ops := by
  delta host_semantic.check_secure_column_loop.body
  all_goals rfl
#print axioms erase_166

/-- Full symbolic source-function equality for `host_semantic.check_secure_column_loop`. -/
theorem erase_167 (ops other : ExternalFuns) :
    @host_semantic.check_secure_column_loop _ (replace ops other) = @host_semantic.check_secure_column_loop _ ops := by
  delta host_semantic.check_secure_column_loop
  try simp only [erase_166 ops other]
  all_goals rfl
#print axioms erase_167

/-- Full symbolic source-function equality for `host_semantic.check_secure_column`. -/
theorem erase_168 (ops other : ExternalFuns) :
    @host_semantic.check_secure_column _ (replace ops other) = @host_semantic.check_secure_column _ ops := by
  delta host_semantic.check_secure_column
  try simp only [erase_167 ops other]
  all_goals rfl
#print axioms erase_168

/-- Full symbolic source-function equality for `host_semantic.check_semantic_columns`. -/
theorem erase_169 (ops other : ExternalFuns) :
    @host_semantic.check_semantic_columns _ (replace ops other) = @host_semantic.check_semantic_columns _ ops := by
  delta host_semantic.check_semantic_columns
  try simp only [erase_168 ops other]
  all_goals rfl
#print axioms erase_169

/-- Full symbolic source-function equality for `host_semantic.append_claim_bytes_loop.body`. -/
theorem erase_170 (ops other : ExternalFuns) :
    @host_semantic.append_claim_bytes_loop.body _ (replace ops other) = @host_semantic.append_claim_bytes_loop.body _ ops := by
  delta host_semantic.append_claim_bytes_loop.body
  all_goals rfl
#print axioms erase_170

/-- Full symbolic source-function equality for `host_semantic.append_claim_bytes_loop`. -/
theorem erase_171 (ops other : ExternalFuns) :
    @host_semantic.append_claim_bytes_loop _ (replace ops other) = @host_semantic.append_claim_bytes_loop _ ops := by
  delta host_semantic.append_claim_bytes_loop
  try simp only [erase_170 ops other]
  all_goals rfl
#print axioms erase_171

/-- Full symbolic source-function equality for `host_semantic.append_claim_bytes`. -/
theorem erase_172 (ops other : ExternalFuns) :
    @host_semantic.append_claim_bytes _ (replace ops other) = @host_semantic.append_claim_bytes _ ops := by
  delta host_semantic.append_claim_bytes
  try simp only [erase_171 ops other]
  all_goals rfl
#print axioms erase_172

/-- Full symbolic source-function equality for `host_semantic.claim_bytes`. -/
theorem erase_173 (ops other : ExternalFuns) :
    @host_semantic.claim_bytes _ (replace ops other) = @host_semantic.claim_bytes _ ops := by
  delta host_semantic.claim_bytes
  try simp only [erase_172 ops other]
  all_goals rfl
#print axioms erase_173

/-- Full symbolic source-function equality for `aspis_core.field.QM31.Insts.CoreCmpEq`. -/
theorem erase_174 (ops other : ExternalFuns) :
    @aspis_core.field.QM31.Insts.CoreCmpEq _ (replace ops other) = @aspis_core.field.QM31.Insts.CoreCmpEq _ ops := by
  delta aspis_core.field.QM31.Insts.CoreCmpEq
  try simp only [erase_60 ops other]
  all_goals rfl
#print axioms erase_174

/-- Full symbolic source-function equality for `aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField`. -/
theorem erase_175 (ops other : ExternalFuns) :
    @aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField _ (replace ops other) = @aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField _ ops := by
  delta aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField
  try simp only [erase_174 ops other, erase_136 ops other]
  all_goals rfl
#print axioms erase_175
end R1Z.PDict_ReachErase
