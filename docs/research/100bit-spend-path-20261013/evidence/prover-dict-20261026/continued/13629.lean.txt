import R1Z.PDict_FmtErase10
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_semantic.column_coefficients`. -/
theorem erase_176 (ops other : ExternalFuns) :
    @host_semantic.column_coefficients _ (replace ops other) = @host_semantic.column_coefficients _ ops := by
  delta host_semantic.column_coefficients
  try simp only [erase_136 ops other]
  all_goals rfl
#print axioms erase_176

/-- Full symbolic source-function equality for `host_semantic.endpoint_bytes_loop.body`. -/
theorem erase_177 (ops other : ExternalFuns) :
    @host_semantic.endpoint_bytes_loop.body _ (replace ops other) = @host_semantic.endpoint_bytes_loop.body _ ops := by
  delta host_semantic.endpoint_bytes_loop.body
  try simp only [erase_175 ops other, erase_176 ops other]
  all_goals rfl
#print axioms erase_177

/-- Full symbolic source-function equality for `host_semantic.endpoint_bytes_loop`. -/
theorem erase_178 (ops other : ExternalFuns) :
    @host_semantic.endpoint_bytes_loop _ (replace ops other) = @host_semantic.endpoint_bytes_loop _ ops := by
  delta host_semantic.endpoint_bytes_loop
  try simp only [erase_177 ops other]
  all_goals rfl
#print axioms erase_178

/-- Full symbolic source-function equality for `host_semantic.endpoint_bytes`. -/
theorem erase_179 (ops other : ExternalFuns) :
    @host_semantic.endpoint_bytes _ (replace ops other) = @host_semantic.endpoint_bytes _ ops := by
  delta host_semantic.endpoint_bytes
  try simp only [erase_178 ops other]
  all_goals rfl
#print axioms erase_179

/-- Full symbolic source-function equality for `host_semantic.extra_claims_loop.body`. -/
theorem erase_180 (ops other : ExternalFuns) :
    @host_semantic.extra_claims_loop.body _ (replace ops other) = @host_semantic.extra_claims_loop.body _ ops := by
  delta host_semantic.extra_claims_loop.body
  try simp only [erase_176 ops other, erase_155 ops other]
  all_goals rfl
#print axioms erase_180

/-- Full symbolic source-function equality for `host_semantic.extra_claims_loop`. -/
theorem erase_181 (ops other : ExternalFuns) :
    @host_semantic.extra_claims_loop _ (replace ops other) = @host_semantic.extra_claims_loop _ ops := by
  delta host_semantic.extra_claims_loop
  try simp only [erase_180 ops other]
  all_goals rfl
#print axioms erase_181

/-- Full symbolic source-function equality for `host_semantic.extra_claims`. -/
theorem erase_182 (ops other : ExternalFuns) :
    @host_semantic.extra_claims _ (replace ops other) = @host_semantic.extra_claims _ ops := by
  delta host_semantic.extra_claims
  try simp only [erase_181 ops other]
  all_goals rfl
#print axioms erase_182

/-- Full symbolic source-function equality for `host_semantic.boolean_point_loop.body`. -/
theorem erase_183 (ops other : ExternalFuns) :
    @host_semantic.boolean_point_loop.body _ (replace ops other) = @host_semantic.boolean_point_loop.body _ ops := by
  delta host_semantic.boolean_point_loop.body
  all_goals rfl
#print axioms erase_183

/-- Full symbolic source-function equality for `host_semantic.boolean_point_loop`. -/
theorem erase_184 (ops other : ExternalFuns) :
    @host_semantic.boolean_point_loop _ (replace ops other) = @host_semantic.boolean_point_loop _ ops := by
  delta host_semantic.boolean_point_loop
  try simp only [erase_183 ops other]
  all_goals rfl
#print axioms erase_184

/-- Full symbolic source-function equality for `host_semantic.boolean_point`. -/
theorem erase_185 (ops other : ExternalFuns) :
    @host_semantic.boolean_point _ (replace ops other) = @host_semantic.boolean_point _ ops := by
  delta host_semantic.boolean_point
  try simp only [erase_184 ops other]
  all_goals rfl
#print axioms erase_185

/-- Full symbolic source-function equality for `host_semantic.initial_mask_value`. -/
theorem erase_186 (ops other : ExternalFuns) :
    @host_semantic.initial_mask_value _ (replace ops other) = @host_semantic.initial_mask_value _ ops := by
  delta host_semantic.initial_mask_value
  try simp only [erase_185 ops other]
  all_goals rfl
#print axioms erase_186

/-- Full symbolic source-function equality for `host_semantic.initial_mask_sum_loop.body`. -/
theorem erase_187 (ops other : ExternalFuns) :
    @host_semantic.initial_mask_sum_loop.body _ (replace ops other) = @host_semantic.initial_mask_sum_loop.body _ ops := by
  delta host_semantic.initial_mask_sum_loop.body
  try simp only [erase_186 ops other]
  all_goals rfl
#print axioms erase_187

/-- Full symbolic source-function equality for `host_semantic.initial_mask_sum_loop`. -/
theorem erase_188 (ops other : ExternalFuns) :
    @host_semantic.initial_mask_sum_loop _ (replace ops other) = @host_semantic.initial_mask_sum_loop _ ops := by
  delta host_semantic.initial_mask_sum_loop
  try simp only [erase_187 ops other]
  all_goals rfl
#print axioms erase_188

/-- Full symbolic source-function equality for `host_semantic.initial_mask_sum`. -/
theorem erase_189 (ops other : ExternalFuns) :
    @host_semantic.initial_mask_sum _ (replace ops other) = @host_semantic.initial_mask_sum _ ops := by
  delta host_semantic.initial_mask_sum
  try simp only [erase_188 ops other]
  all_goals rfl
#print axioms erase_189

/-- Full symbolic source-function equality for `host_semantic.lift`. -/
theorem erase_190 (ops other : ExternalFuns) :
    @host_semantic.lift _ (replace ops other) = @host_semantic.lift _ ops := by
  delta host_semantic.lift
  all_goals rfl
#print axioms erase_190

/-- Full symbolic source-function equality for `host_semantic.lift_columns_loop0_loop0.body`. -/
theorem erase_191 (ops other : ExternalFuns) :
    @host_semantic.lift_columns_loop0_loop0.body _ (replace ops other) = @host_semantic.lift_columns_loop0_loop0.body _ ops := by
  delta host_semantic.lift_columns_loop0_loop0.body
  try simp only [erase_190 ops other]
  all_goals rfl
#print axioms erase_191
end R1Z.PDict_FmtErase
