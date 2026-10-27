import R1Z.PDict_FmtErase14
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_wire.SemanticTranscript.new`. -/
theorem erase_240 (ops other : ExternalFuns) :
    @host_wire.SemanticTranscript.new _ (replace ops other) = @host_wire.SemanticTranscript.new _ ops := by
  delta host_wire.SemanticTranscript.new
  all_goals rfl
#print axioms erase_240

/-- Full symbolic source-function equality for `host_semantic.build_with_helper_mode`. -/
theorem erase_241 (ops other : ExternalFuns) :
    @host_semantic.build_with_helper_mode _ (replace ops other) = @host_semantic.build_with_helper_mode _ ops := by
  delta host_semantic.build_with_helper_mode
  try simp only [erase_60 ops other, erase_136 ops other, erase_148 ops other, erase_149 ops other, erase_162 ops other, erase_165 ops other, erase_169 ops other, erase_173 ops other, erase_179 ops other, erase_182 ops other, erase_189 ops other, erase_195 ops other, erase_160 ops other, erase_204 ops other, erase_207 ops other, erase_238 ops other, erase_239 ops other, erase_240 ops other, erase_203 ops other]
  all_goals rfl
#print axioms erase_241

/-- Full symbolic source-function equality for `host_semantic.copy_cell`. -/
theorem erase_242 (ops other : ExternalFuns) :
    @host_semantic.copy_cell _ (replace ops other) = @host_semantic.copy_cell _ ops := by
  delta host_semantic.copy_cell
  all_goals rfl
#print axioms erase_242

/-- Full symbolic source-function equality for `host_semantic.copy_tuple_limb`. -/
theorem erase_243 (ops other : ExternalFuns) :
    @host_semantic.copy_tuple_limb _ (replace ops other) = @host_semantic.copy_tuple_limb _ ops := by
  delta host_semantic.copy_tuple_limb
  try simp only [erase_242 ops other]
  all_goals rfl
#print axioms erase_243

/-- Full symbolic source-function equality for `host_semantic.copy_tuple_values`. -/
theorem erase_244 (ops other : ExternalFuns) :
    @host_semantic.copy_tuple_values _ (replace ops other) = @host_semantic.copy_tuple_values _ ops := by
  delta host_semantic.copy_tuple_values
  try simp only [erase_243 ops other]
  all_goals rfl
#print axioms erase_244

/-- Full symbolic source-function equality for `host_semantic.copy_endpoint_values`. -/
theorem erase_245 (ops other : ExternalFuns) :
    @host_semantic.copy_endpoint_values _ (replace ops other) = @host_semantic.copy_endpoint_values _ ops := by
  delta host_semantic.copy_endpoint_values
  try simp only [erase_244 ops other]
  all_goals rfl
#print axioms erase_245

/-- Full symbolic source-function equality for `host_semantic.lean_copy_row_values_loop.body`. -/
theorem erase_246 (ops other : ExternalFuns) :
    @host_semantic.lean_copy_row_values_loop.body _ (replace ops other) = @host_semantic.lean_copy_row_values_loop.body _ ops := by
  delta host_semantic.lean_copy_row_values_loop.body
  try simp only [erase_245 ops other]
  all_goals rfl
#print axioms erase_246

/-- Full symbolic source-function equality for `host_semantic.lean_copy_row_values_loop`. -/
theorem erase_247 (ops other : ExternalFuns) :
    @host_semantic.lean_copy_row_values_loop _ (replace ops other) = @host_semantic.lean_copy_row_values_loop _ ops := by
  delta host_semantic.lean_copy_row_values_loop
  try simp only [erase_246 ops other]
  all_goals rfl
#print axioms erase_247

/-- Full symbolic source-function equality for `host_semantic.lean_copy_row_values`. -/
theorem erase_248 (ops other : ExternalFuns) :
    @host_semantic.lean_copy_row_values _ (replace ops other) = @host_semantic.lean_copy_row_values _ ops := by
  delta host_semantic.lean_copy_row_values
  try simp only [erase_101 ops other, erase_247 ops other]
  all_goals rfl
#print axioms erase_248

/-- Full symbolic source-function equality for `host_semantic.no_pole`. -/
theorem erase_249 (ops other : ExternalFuns) :
    @host_semantic.no_pole _ (replace ops other) = @host_semantic.no_pole _ ops := by
  delta host_semantic.no_pole
  try simp only [erase_248 ops other]
  all_goals rfl
#print axioms erase_249

/-- Full symbolic source-function equality for `host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once`. -/
theorem erase_250 (ops other : ExternalFuns) :
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once _ (replace ops other) = @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once _ ops := by
  delta host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once
  try simp only [erase_249 ops other]
  all_goals rfl
#print axioms erase_250

/-- Full symbolic source-function equality for `host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error`. -/
theorem erase_251 (ops other : ExternalFuns) :
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error _ (replace ops other) = @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error _ ops := by
  delta host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
  try simp only [erase_250 ops other]
  all_goals rfl
#print axioms erase_251

/-- Full symbolic source-function equality for `host_semantic.clone_semantic_columns_loop0.body`. -/
theorem erase_252 (ops other : ExternalFuns) :
    @host_semantic.clone_semantic_columns_loop0.body _ (replace ops other) = @host_semantic.clone_semantic_columns_loop0.body _ ops := by
  delta host_semantic.clone_semantic_columns_loop0.body
  try simp only [erase_117 ops other]
  all_goals rfl
#print axioms erase_252

/-- Full symbolic source-function equality for `host_semantic.clone_semantic_columns_loop0`. -/
theorem erase_253 (ops other : ExternalFuns) :
    @host_semantic.clone_semantic_columns_loop0 _ (replace ops other) = @host_semantic.clone_semantic_columns_loop0 _ ops := by
  delta host_semantic.clone_semantic_columns_loop0
  try simp only [erase_252 ops other]
  all_goals rfl
#print axioms erase_253

/-- Full symbolic source-function equality for `host_semantic.clone_semantic_columns_loop1.body`. -/
theorem erase_254 (ops other : ExternalFuns) :
    @host_semantic.clone_semantic_columns_loop1.body _ (replace ops other) = @host_semantic.clone_semantic_columns_loop1.body _ ops := by
  delta host_semantic.clone_semantic_columns_loop1.body
  try simp only [erase_117 ops other]
  all_goals rfl
#print axioms erase_254

/-- Full symbolic source-function equality for `host_semantic.clone_semantic_columns_loop1`. -/
theorem erase_255 (ops other : ExternalFuns) :
    @host_semantic.clone_semantic_columns_loop1 _ (replace ops other) = @host_semantic.clone_semantic_columns_loop1 _ ops := by
  delta host_semantic.clone_semantic_columns_loop1
  try simp only [erase_254 ops other]
  all_goals rfl
#print axioms erase_255
end R1Z.PDict_FmtErase
