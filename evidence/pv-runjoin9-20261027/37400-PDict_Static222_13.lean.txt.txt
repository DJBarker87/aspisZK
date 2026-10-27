import R1Z.PDict_Static222_12
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_sumcheck.encode_polynomial_loop.body`. -/
theorem erase_208 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.encode_polynomial_loop.body (types base F) (selected base F ops) = @host_sumcheck.encode_polynomial_loop.body base ops := by
  delta host_sumcheck.encode_polynomial_loop.body
  all_goals rfl
#print axioms erase_208

/-- Carrier transport candidate for `host_sumcheck.encode_polynomial_loop`. -/
theorem erase_209 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.encode_polynomial_loop (types base F) (selected base F ops) = @host_sumcheck.encode_polynomial_loop base ops := by
  delta host_sumcheck.encode_polynomial_loop
  try simp only [erase_208 base F ops]
  all_goals rfl
#print axioms erase_209

/-- Carrier transport candidate for `host_sumcheck.encode_polynomial`. -/
theorem erase_210 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.encode_polynomial (types base F) (selected base F ops) = @host_sumcheck.encode_polynomial base ops := by
  delta host_sumcheck.encode_polynomial
  try simp only [erase_209 base F ops]
  all_goals rfl
#print axioms erase_210

/-- Carrier transport candidate for `host_sumcheck.interpolation_accumulate_loop.body`. -/
theorem erase_211 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_accumulate_loop.body (types base F) (selected base F ops) = @host_sumcheck.interpolation_accumulate_loop.body base ops := by
  delta host_sumcheck.interpolation_accumulate_loop.body
  all_goals rfl
#print axioms erase_211

/-- Carrier transport candidate for `host_sumcheck.interpolation_accumulate_loop`. -/
theorem erase_212 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_accumulate_loop (types base F) (selected base F ops) = @host_sumcheck.interpolation_accumulate_loop base ops := by
  delta host_sumcheck.interpolation_accumulate_loop
  try simp only [erase_211 base F ops]
  all_goals rfl
#print axioms erase_212

/-- Carrier transport candidate for `host_sumcheck.interpolation_accumulate`. -/
theorem erase_213 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_accumulate (types base F) (selected base F ops) = @host_sumcheck.interpolation_accumulate base ops := by
  delta host_sumcheck.interpolation_accumulate
  try simp only [erase_212 base F ops]
  all_goals rfl
#print axioms erase_213

/-- Carrier transport candidate for `host_sumcheck.interpolation_shift`. -/
theorem erase_214 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_shift (types base F) (selected base F ops) = @host_sumcheck.interpolation_shift base ops := by
  delta host_sumcheck.interpolation_shift
  all_goals rfl
#print axioms erase_214

/-- Carrier transport candidate for `host_sumcheck.interpolation_basis_cell`. -/
theorem erase_215 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_basis_cell (types base F) (selected base F ops) = @host_sumcheck.interpolation_basis_cell base ops := by
  delta host_sumcheck.interpolation_basis_cell
  try simp only [erase_214 base F ops]
  all_goals rfl
#print axioms erase_215

/-- Carrier transport candidate for `host_sumcheck.interpolation_extend_loop.body`. -/
theorem erase_216 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_extend_loop.body (types base F) (selected base F ops) = @host_sumcheck.interpolation_extend_loop.body base ops := by
  delta host_sumcheck.interpolation_extend_loop.body
  try simp only [erase_215 base F ops]
  all_goals rfl
#print axioms erase_216

/-- Carrier transport candidate for `host_sumcheck.interpolation_extend_loop`. -/
theorem erase_217 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_extend_loop (types base F) (selected base F ops) = @host_sumcheck.interpolation_extend_loop base ops := by
  delta host_sumcheck.interpolation_extend_loop
  try simp only [erase_216 base F ops]
  all_goals rfl
#print axioms erase_217

/-- Carrier transport candidate for `host_sumcheck.interpolation_extend`. -/
theorem erase_218 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_extend (types base F) (selected base F ops) = @host_sumcheck.interpolation_extend base ops := by
  delta host_sumcheck.interpolation_extend
  try simp only [erase_217 base F ops]
  all_goals rfl
#print axioms erase_218

/-- Carrier transport candidate for `host_sumcheck.interpolation_basis_steps`. -/
theorem erase_219 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_basis_steps (types base F) (selected base F ops) = @host_sumcheck.interpolation_basis_steps base ops := by
  delta host_sumcheck.interpolation_basis_steps
  try simp only [erase_218 base F ops]
  all_goals rfl
#print axioms erase_219

/-- Carrier transport candidate for `host_sumcheck.interpolation_basis`. -/
theorem erase_220 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolation_basis (types base F) (selected base F ops) = @host_sumcheck.interpolation_basis base ops := by
  delta host_sumcheck.interpolation_basis
  try simp only [erase_219 base F ops]
  all_goals rfl
#print axioms erase_220

/-- Carrier transport candidate for `host_sumcheck.interpolate_loop.body`. -/
theorem erase_221 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolate_loop.body (types base F) (selected base F ops) = @host_sumcheck.interpolate_loop.body base ops := by
  delta host_sumcheck.interpolate_loop.body
  try simp only [erase_213 base F ops, erase_220 base F ops]
  all_goals rfl
#print axioms erase_221

/-- Carrier transport candidate for `host_sumcheck.interpolate_loop`. -/
theorem erase_222 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolate_loop (types base F) (selected base F ops) = @host_sumcheck.interpolate_loop base ops := by
  delta host_sumcheck.interpolate_loop
  try simp only [erase_221 base F ops]
  all_goals rfl
#print axioms erase_222

/-- Carrier transport candidate for `host_sumcheck.interpolate`. -/
theorem erase_223 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_sumcheck.interpolate (types base F) (selected base F ops) = @host_sumcheck.interpolate base ops := by
  delta host_sumcheck.interpolate
  try simp only [erase_222 base F ops]
  all_goals rfl
#print axioms erase_223
end R1Z.PDict_Static222
