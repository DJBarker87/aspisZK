import R1Z.PDict_Static222_10
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_semantic.column_coefficients`. -/
theorem erase_176 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.column_coefficients (types base F) (selected base F ops) = @host_semantic.column_coefficients base ops := by
  delta host_semantic.column_coefficients
  try simp only [erase_136 base F ops]
  all_goals rfl
#print axioms erase_176

/-- Carrier transport candidate for `host_semantic.endpoint_bytes_loop.body`. -/
theorem erase_177 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.endpoint_bytes_loop.body (types base F) (selected base F ops) = @host_semantic.endpoint_bytes_loop.body base ops := by
  delta host_semantic.endpoint_bytes_loop.body
  try simp only [erase_175 base F ops, erase_176 base F ops]
  all_goals rfl
#print axioms erase_177

/-- Carrier transport candidate for `host_semantic.endpoint_bytes_loop`. -/
theorem erase_178 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.endpoint_bytes_loop (types base F) (selected base F ops) = @host_semantic.endpoint_bytes_loop base ops := by
  delta host_semantic.endpoint_bytes_loop
  try simp only [erase_177 base F ops]
  all_goals rfl
#print axioms erase_178

/-- Carrier transport candidate for `host_semantic.endpoint_bytes`. -/
theorem erase_179 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.endpoint_bytes (types base F) (selected base F ops) = @host_semantic.endpoint_bytes base ops := by
  delta host_semantic.endpoint_bytes
  try simp only [erase_178 base F ops]
  all_goals rfl
#print axioms erase_179

/-- Carrier transport candidate for `host_semantic.extra_claims_loop.body`. -/
theorem erase_180 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_claims_loop.body (types base F) (selected base F ops) = @host_semantic.extra_claims_loop.body base ops := by
  delta host_semantic.extra_claims_loop.body
  try simp only [erase_176 base F ops, erase_155 base F ops]
  all_goals rfl
#print axioms erase_180

/-- Carrier transport candidate for `host_semantic.extra_claims_loop`. -/
theorem erase_181 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_claims_loop (types base F) (selected base F ops) = @host_semantic.extra_claims_loop base ops := by
  delta host_semantic.extra_claims_loop
  try simp only [erase_180 base F ops]
  all_goals rfl
#print axioms erase_181

/-- Carrier transport candidate for `host_semantic.extra_claims`. -/
theorem erase_182 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_claims (types base F) (selected base F ops) = @host_semantic.extra_claims base ops := by
  delta host_semantic.extra_claims
  try simp only [erase_181 base F ops]
  all_goals rfl
#print axioms erase_182

/-- Carrier transport candidate for `host_semantic.boolean_point_loop.body`. -/
theorem erase_183 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.boolean_point_loop.body (types base F) (selected base F ops) = @host_semantic.boolean_point_loop.body base ops := by
  delta host_semantic.boolean_point_loop.body
  all_goals rfl
#print axioms erase_183

/-- Carrier transport candidate for `host_semantic.boolean_point_loop`. -/
theorem erase_184 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.boolean_point_loop (types base F) (selected base F ops) = @host_semantic.boolean_point_loop base ops := by
  delta host_semantic.boolean_point_loop
  try simp only [erase_183 base F ops]
  all_goals rfl
#print axioms erase_184

/-- Carrier transport candidate for `host_semantic.boolean_point`. -/
theorem erase_185 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.boolean_point (types base F) (selected base F ops) = @host_semantic.boolean_point base ops := by
  delta host_semantic.boolean_point
  try simp only [erase_184 base F ops]
  all_goals rfl
#print axioms erase_185

/-- Carrier transport candidate for `host_semantic.initial_mask_value`. -/
theorem erase_186 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.initial_mask_value (types base F) (selected base F ops) = @host_semantic.initial_mask_value base ops := by
  delta host_semantic.initial_mask_value
  try simp only [erase_185 base F ops]
  all_goals rfl
#print axioms erase_186

/-- Carrier transport candidate for `host_semantic.initial_mask_sum_loop.body`. -/
theorem erase_187 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.initial_mask_sum_loop.body (types base F) (selected base F ops) = @host_semantic.initial_mask_sum_loop.body base ops := by
  delta host_semantic.initial_mask_sum_loop.body
  try simp only [erase_186 base F ops]
  all_goals rfl
#print axioms erase_187

/-- Carrier transport candidate for `host_semantic.initial_mask_sum_loop`. -/
theorem erase_188 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.initial_mask_sum_loop (types base F) (selected base F ops) = @host_semantic.initial_mask_sum_loop base ops := by
  delta host_semantic.initial_mask_sum_loop
  try simp only [erase_187 base F ops]
  all_goals rfl
#print axioms erase_188

/-- Carrier transport candidate for `host_semantic.initial_mask_sum`. -/
theorem erase_189 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.initial_mask_sum (types base F) (selected base F ops) = @host_semantic.initial_mask_sum base ops := by
  delta host_semantic.initial_mask_sum
  try simp only [erase_188 base F ops]
  all_goals rfl
#print axioms erase_189

/-- Carrier transport candidate for `host_semantic.lift`. -/
theorem erase_190 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift (types base F) (selected base F ops) = @host_semantic.lift base ops := by
  delta host_semantic.lift
  all_goals rfl
#print axioms erase_190

/-- Carrier transport candidate for `host_semantic.lift_columns_loop0_loop0.body`. -/
theorem erase_191 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift_columns_loop0_loop0.body (types base F) (selected base F ops) = @host_semantic.lift_columns_loop0_loop0.body base ops := by
  delta host_semantic.lift_columns_loop0_loop0.body
  try simp only [erase_190 base F ops]
  all_goals rfl
#print axioms erase_191
end R1Z.PDict_Static222
