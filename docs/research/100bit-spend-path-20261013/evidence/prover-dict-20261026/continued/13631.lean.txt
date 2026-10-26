import R1Z.PDict_FmtErase12
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_sumcheck.encode_polynomial_loop.body`. -/
theorem erase_208 (ops other : ExternalFuns) :
    @host_sumcheck.encode_polynomial_loop.body _ (replace ops other) = @host_sumcheck.encode_polynomial_loop.body _ ops := by
  delta host_sumcheck.encode_polynomial_loop.body
  all_goals rfl
#print axioms erase_208

/-- Full symbolic source-function equality for `host_sumcheck.encode_polynomial_loop`. -/
theorem erase_209 (ops other : ExternalFuns) :
    @host_sumcheck.encode_polynomial_loop _ (replace ops other) = @host_sumcheck.encode_polynomial_loop _ ops := by
  delta host_sumcheck.encode_polynomial_loop
  try simp only [erase_208 ops other]
  all_goals rfl
#print axioms erase_209

/-- Full symbolic source-function equality for `host_sumcheck.encode_polynomial`. -/
theorem erase_210 (ops other : ExternalFuns) :
    @host_sumcheck.encode_polynomial _ (replace ops other) = @host_sumcheck.encode_polynomial _ ops := by
  delta host_sumcheck.encode_polynomial
  try simp only [erase_209 ops other]
  all_goals rfl
#print axioms erase_210

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_accumulate_loop.body`. -/
theorem erase_211 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_accumulate_loop.body _ (replace ops other) = @host_sumcheck.interpolation_accumulate_loop.body _ ops := by
  delta host_sumcheck.interpolation_accumulate_loop.body
  all_goals rfl
#print axioms erase_211

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_accumulate_loop`. -/
theorem erase_212 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_accumulate_loop _ (replace ops other) = @host_sumcheck.interpolation_accumulate_loop _ ops := by
  delta host_sumcheck.interpolation_accumulate_loop
  try simp only [erase_211 ops other]
  all_goals rfl
#print axioms erase_212

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_accumulate`. -/
theorem erase_213 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_accumulate _ (replace ops other) = @host_sumcheck.interpolation_accumulate _ ops := by
  delta host_sumcheck.interpolation_accumulate
  try simp only [erase_212 ops other]
  all_goals rfl
#print axioms erase_213

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_shift`. -/
theorem erase_214 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_shift _ (replace ops other) = @host_sumcheck.interpolation_shift _ ops := by
  delta host_sumcheck.interpolation_shift
  all_goals rfl
#print axioms erase_214

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_basis_cell`. -/
theorem erase_215 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_basis_cell _ (replace ops other) = @host_sumcheck.interpolation_basis_cell _ ops := by
  delta host_sumcheck.interpolation_basis_cell
  try simp only [erase_214 ops other]
  all_goals rfl
#print axioms erase_215

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_extend_loop.body`. -/
theorem erase_216 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_extend_loop.body _ (replace ops other) = @host_sumcheck.interpolation_extend_loop.body _ ops := by
  delta host_sumcheck.interpolation_extend_loop.body
  try simp only [erase_215 ops other]
  all_goals rfl
#print axioms erase_216

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_extend_loop`. -/
theorem erase_217 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_extend_loop _ (replace ops other) = @host_sumcheck.interpolation_extend_loop _ ops := by
  delta host_sumcheck.interpolation_extend_loop
  try simp only [erase_216 ops other]
  all_goals rfl
#print axioms erase_217

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_extend`. -/
theorem erase_218 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_extend _ (replace ops other) = @host_sumcheck.interpolation_extend _ ops := by
  delta host_sumcheck.interpolation_extend
  try simp only [erase_217 ops other]
  all_goals rfl
#print axioms erase_218

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_basis_steps`. -/
theorem erase_219 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_basis_steps _ (replace ops other) = @host_sumcheck.interpolation_basis_steps _ ops := by
  delta host_sumcheck.interpolation_basis_steps
  try simp only [erase_218 ops other]
  all_goals rfl
#print axioms erase_219

/-- Full symbolic source-function equality for `host_sumcheck.interpolation_basis`. -/
theorem erase_220 (ops other : ExternalFuns) :
    @host_sumcheck.interpolation_basis _ (replace ops other) = @host_sumcheck.interpolation_basis _ ops := by
  delta host_sumcheck.interpolation_basis
  try simp only [erase_219 ops other]
  all_goals rfl
#print axioms erase_220

/-- Full symbolic source-function equality for `host_sumcheck.interpolate_loop.body`. -/
theorem erase_221 (ops other : ExternalFuns) :
    @host_sumcheck.interpolate_loop.body _ (replace ops other) = @host_sumcheck.interpolate_loop.body _ ops := by
  delta host_sumcheck.interpolate_loop.body
  try simp only [erase_213 ops other, erase_220 ops other]
  all_goals rfl
#print axioms erase_221

/-- Full symbolic source-function equality for `host_sumcheck.interpolate_loop`. -/
theorem erase_222 (ops other : ExternalFuns) :
    @host_sumcheck.interpolate_loop _ (replace ops other) = @host_sumcheck.interpolate_loop _ ops := by
  delta host_sumcheck.interpolate_loop
  try simp only [erase_221 ops other]
  all_goals rfl
#print axioms erase_222

/-- Full symbolic source-function equality for `host_sumcheck.interpolate`. -/
theorem erase_223 (ops other : ExternalFuns) :
    @host_sumcheck.interpolate _ (replace ops other) = @host_sumcheck.interpolate _ ops := by
  delta host_sumcheck.interpolate
  try simp only [erase_222 ops other]
  all_goals rfl
#print axioms erase_223
end R1Z.PDict_FmtErase
