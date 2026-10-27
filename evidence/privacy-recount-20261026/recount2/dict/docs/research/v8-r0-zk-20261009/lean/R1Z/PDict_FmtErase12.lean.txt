import R1Z.PDict_FmtErase11
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `host_semantic.lift_columns_loop0_loop0`. -/
theorem erase_192 (ops other : ExternalFuns) :
    @host_semantic.lift_columns_loop0_loop0 _ (replace ops other) = @host_semantic.lift_columns_loop0_loop0 _ ops := by
  delta host_semantic.lift_columns_loop0_loop0
  try simp only [erase_191 ops other]
  all_goals rfl
#print axioms erase_192

/-- Full symbolic source-function equality for `host_semantic.lift_columns_loop0.body`. -/
theorem erase_193 (ops other : ExternalFuns) :
    @host_semantic.lift_columns_loop0.body _ (replace ops other) = @host_semantic.lift_columns_loop0.body _ ops := by
  delta host_semantic.lift_columns_loop0.body
  try simp only [erase_192 ops other]
  all_goals rfl
#print axioms erase_193

/-- Full symbolic source-function equality for `host_semantic.lift_columns_loop0`. -/
theorem erase_194 (ops other : ExternalFuns) :
    @host_semantic.lift_columns_loop0 _ (replace ops other) = @host_semantic.lift_columns_loop0 _ ops := by
  delta host_semantic.lift_columns_loop0
  try simp only [erase_193 ops other]
  all_goals rfl
#print axioms erase_194

/-- Full symbolic source-function equality for `host_semantic.lift_columns`. -/
theorem erase_195 (ops other : ExternalFuns) :
    @host_semantic.lift_columns _ (replace ops other) = @host_semantic.lift_columns _ ops := by
  delta host_semantic.lift_columns
  try simp only [erase_63 ops other, erase_101 ops other, erase_194 ops other]
  all_goals rfl
#print axioms erase_195

/-- Full symbolic source-function equality for `host_wire.validate_record_fields_loop.body`. -/
theorem erase_196 (ops other : ExternalFuns) :
    @host_wire.validate_record_fields_loop.body _ (replace ops other) = @host_wire.validate_record_fields_loop.body _ ops := by
  delta host_wire.validate_record_fields_loop.body
  try simp only [erase_60 ops other]
  all_goals rfl
#print axioms erase_196

/-- Full symbolic source-function equality for `host_wire.validate_record_fields_loop`. -/
theorem erase_197 (ops other : ExternalFuns) :
    @host_wire.validate_record_fields_loop _ (replace ops other) = @host_wire.validate_record_fields_loop _ ops := by
  delta host_wire.validate_record_fields_loop
  try simp only [erase_196 ops other]
  all_goals rfl
#print axioms erase_197

/-- Full symbolic source-function equality for `host_wire.validate_record_fields`. -/
theorem erase_198 (ops other : ExternalFuns) :
    @host_wire.validate_record_fields _ (replace ops other) = @host_wire.validate_record_fields _ ops := by
  delta host_wire.validate_record_fields
  try simp only [erase_197 ops other]
  all_goals rfl
#print axioms erase_198

/-- Full symbolic source-function equality for `r1_wire.row_shape`. -/
theorem erase_199 (ops other : ExternalFuns) :
    @r1_wire.row_shape _ (replace ops other) = @r1_wire.row_shape _ ops := by
  delta r1_wire.row_shape
  all_goals rfl
#print axioms erase_199

/-- Full symbolic source-function equality for `host_wire.parse_record`. -/
theorem erase_200 (ops other : ExternalFuns) :
    @host_wire.parse_record _ (replace ops other) = @host_wire.parse_record _ ops := by
  delta host_wire.parse_record
  try simp only [erase_198 ops other, erase_199 ops other]
  all_goals rfl
#print axioms erase_200

/-- Full symbolic source-function equality for `host_wire.SemanticTranscript.sample_block`. -/
theorem erase_201 (ops other : ExternalFuns) :
    @host_wire.SemanticTranscript.sample_block _ (replace ops other) = @host_wire.SemanticTranscript.sample_block _ ops := by
  delta host_wire.SemanticTranscript.sample_block
  try simp only [erase_200 ops other]
  all_goals rfl
#print axioms erase_201

/-- Full symbolic source-function equality for `host_wire.SemanticTranscript.semantic`. -/
theorem erase_202 (ops other : ExternalFuns) :
    @host_wire.SemanticTranscript.semantic _ (replace ops other) = @host_wire.SemanticTranscript.semantic _ ops := by
  delta host_wire.SemanticTranscript.semantic
  try simp only [erase_201 ops other]
  all_goals rfl
#print axioms erase_202

/-- Full symbolic source-function equality for `host_wire.record`. -/
theorem erase_203 (ops other : ExternalFuns) :
    @host_wire.record _ (replace ops other) = @host_wire.record _ ops := by
  delta host_wire.record
  try simp only [erase_200 ops other, erase_199 ops other]
  all_goals rfl
#print axioms erase_203

/-- Full symbolic source-function equality for `host_semantic.semantic_row`. -/
theorem erase_204 (ops other : ExternalFuns) :
    @host_semantic.semantic_row _ (replace ops other) = @host_semantic.semantic_row _ ops := by
  delta host_semantic.semantic_row
  try simp only [erase_202 ops other, erase_203 ops other]
  all_goals rfl
#print axioms erase_204

/-- Full symbolic source-function equality for `host_semantic.zc_rows_loop.body`. -/
theorem erase_205 (ops other : ExternalFuns) :
    @host_semantic.zc_rows_loop.body _ (replace ops other) = @host_semantic.zc_rows_loop.body _ ops := by
  delta host_semantic.zc_rows_loop.body
  try simp only [erase_204 ops other]
  all_goals rfl
#print axioms erase_205

/-- Full symbolic source-function equality for `host_semantic.zc_rows_loop`. -/
theorem erase_206 (ops other : ExternalFuns) :
    @host_semantic.zc_rows_loop _ (replace ops other) = @host_semantic.zc_rows_loop _ ops := by
  delta host_semantic.zc_rows_loop
  try simp only [erase_205 ops other]
  all_goals rfl
#print axioms erase_206

/-- Full symbolic source-function equality for `host_semantic.zc_rows`. -/
theorem erase_207 (ops other : ExternalFuns) :
    @host_semantic.zc_rows _ (replace ops other) = @host_semantic.zc_rows _ ops := by
  delta host_semantic.zc_rows
  try simp only [erase_206 ops other]
  all_goals rfl
#print axioms erase_207
end R1Z.PDict_FmtErase
