import R1Z.PDict_Static222_11
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_semantic.lift_columns_loop0_loop0`. -/
theorem erase_192 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift_columns_loop0_loop0 (types base F) (selected base F ops) = @host_semantic.lift_columns_loop0_loop0 base ops := by
  delta host_semantic.lift_columns_loop0_loop0
  try simp only [erase_191 base F ops]
  all_goals rfl
#print axioms erase_192

/-- Carrier transport candidate for `host_semantic.lift_columns_loop0.body`. -/
theorem erase_193 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift_columns_loop0.body (types base F) (selected base F ops) = @host_semantic.lift_columns_loop0.body base ops := by
  delta host_semantic.lift_columns_loop0.body
  try simp only [erase_192 base F ops]
  all_goals rfl
#print axioms erase_193

/-- Carrier transport candidate for `host_semantic.lift_columns_loop0`. -/
theorem erase_194 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift_columns_loop0 (types base F) (selected base F ops) = @host_semantic.lift_columns_loop0 base ops := by
  delta host_semantic.lift_columns_loop0
  try simp only [erase_193 base F ops]
  all_goals rfl
#print axioms erase_194

/-- Carrier transport candidate for `host_semantic.lift_columns`. -/
theorem erase_195 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.lift_columns (types base F) (selected base F ops) = @host_semantic.lift_columns base ops := by
  delta host_semantic.lift_columns
  try simp only [erase_63 base F ops, erase_101 base F ops, erase_194 base F ops]
  all_goals rfl
#print axioms erase_195

/-- Carrier transport candidate for `host_wire.validate_record_fields_loop.body`. -/
theorem erase_196 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.validate_record_fields_loop.body (types base F) (selected base F ops) = @host_wire.validate_record_fields_loop.body base ops := by
  delta host_wire.validate_record_fields_loop.body
  try simp only [erase_60 base F ops]
  all_goals rfl
#print axioms erase_196

/-- Carrier transport candidate for `host_wire.validate_record_fields_loop`. -/
theorem erase_197 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.validate_record_fields_loop (types base F) (selected base F ops) = @host_wire.validate_record_fields_loop base ops := by
  delta host_wire.validate_record_fields_loop
  try simp only [erase_196 base F ops]
  all_goals rfl
#print axioms erase_197

/-- Carrier transport candidate for `host_wire.validate_record_fields`. -/
theorem erase_198 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.validate_record_fields (types base F) (selected base F ops) = @host_wire.validate_record_fields base ops := by
  delta host_wire.validate_record_fields
  try simp only [erase_197 base F ops]
  all_goals rfl
#print axioms erase_198

/-- Carrier transport candidate for `r1_wire.row_shape`. -/
theorem erase_199 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @r1_wire.row_shape (types base F) (selected base F ops) = @r1_wire.row_shape base ops := by
  delta r1_wire.row_shape
  all_goals rfl
#print axioms erase_199

/-- Carrier transport candidate for `host_wire.parse_record`. -/
theorem erase_200 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.parse_record (types base F) (selected base F ops) = @host_wire.parse_record base ops := by
  delta host_wire.parse_record
  try simp only [erase_198 base F ops, erase_199 base F ops]
  all_goals rfl
#print axioms erase_200

/-- Carrier transport candidate for `host_wire.SemanticTranscript.sample_block`. -/
theorem erase_201 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.SemanticTranscript.sample_block (types base F) (selected base F ops) = @host_wire.SemanticTranscript.sample_block base ops := by
  delta host_wire.SemanticTranscript.sample_block
  try simp only [erase_200 base F ops]
  all_goals rfl
#print axioms erase_201

/-- Carrier transport candidate for `host_wire.SemanticTranscript.semantic`. -/
theorem erase_202 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.SemanticTranscript.semantic (types base F) (selected base F ops) = @host_wire.SemanticTranscript.semantic base ops := by
  delta host_wire.SemanticTranscript.semantic
  try simp only [erase_201 base F ops]
  all_goals rfl
#print axioms erase_202

/-- Carrier transport candidate for `host_wire.record`. -/
theorem erase_203 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.record (types base F) (selected base F ops) = @host_wire.record base ops := by
  delta host_wire.record
  try simp only [erase_200 base F ops, erase_199 base F ops]
  all_goals rfl
#print axioms erase_203

/-- Carrier transport candidate for `host_semantic.semantic_row`. -/
theorem erase_204 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.semantic_row (types base F) (selected base F ops) = @host_semantic.semantic_row base ops := by
  delta host_semantic.semantic_row
  try simp only [erase_202 base F ops, erase_203 base F ops]
  all_goals rfl
#print axioms erase_204

/-- Carrier transport candidate for `host_semantic.zc_rows_loop.body`. -/
theorem erase_205 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.zc_rows_loop.body (types base F) (selected base F ops) = @host_semantic.zc_rows_loop.body base ops := by
  delta host_semantic.zc_rows_loop.body
  try simp only [erase_204 base F ops]
  all_goals rfl
#print axioms erase_205

/-- Carrier transport candidate for `host_semantic.zc_rows_loop`. -/
theorem erase_206 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.zc_rows_loop (types base F) (selected base F ops) = @host_semantic.zc_rows_loop base ops := by
  delta host_semantic.zc_rows_loop
  try simp only [erase_205 base F ops]
  all_goals rfl
#print axioms erase_206

/-- Carrier transport candidate for `host_semantic.zc_rows`. -/
theorem erase_207 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.zc_rows (types base F) (selected base F ops) = @host_semantic.zc_rows base ops := by
  delta host_semantic.zc_rows
  try simp only [erase_206 base F ops]
  all_goals rfl
#print axioms erase_207
end R1Z.PDict_Static222
