import R1Z.PDict_Static222_14
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `host_wire.SemanticTranscript.new`. -/
theorem erase_240 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_wire.SemanticTranscript.new (types base F) (selected base F ops) = @host_wire.SemanticTranscript.new base ops := by
  delta host_wire.SemanticTranscript.new
  all_goals rfl
#print axioms erase_240

/-- Carrier transport candidate for `host_semantic.copy_cell`. -/
theorem erase_242 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.copy_cell (types base F) (selected base F ops) = @host_semantic.copy_cell base ops := by
  delta host_semantic.copy_cell
  all_goals rfl
#print axioms erase_242

/-- Pointwise structural transport for `host_semantic.copy_tuple_limb`. -/
theorem erase_243 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    letI : ExternalTypes := base
    ∀ (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (limb : aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1),
    @host_semantic.copy_tuple_limb (types base F) (selected base F ops) (PDict_FormatterTypeMaps.trace base F trace) limb =
    @host_semantic.copy_tuple_limb base ops trace limb := by
  intro trace limb
  delta host_semantic.copy_tuple_limb
  try simp only [erase_242 base F ops, PDict_FormatterTypeMaps.trace, PDict_FormatterTypeMaps.compilation]
  all_goals rfl
#print axioms erase_243

/-- Pointwise structural transport for `host_semantic.copy_tuple_values`. -/
theorem erase_244 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    letI : ExternalTypes := base
    ∀ (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1),
    @host_semantic.copy_tuple_values (types base F) (selected base F ops) (PDict_FormatterTypeMaps.trace base F trace) tuple =
    @host_semantic.copy_tuple_values base ops trace tuple := by
  intro trace tuple
  delta host_semantic.copy_tuple_values
  try simp only [erase_243 base F ops, PDict_FormatterTypeMaps.trace, PDict_FormatterTypeMaps.compilation]
  all_goals rfl
#print axioms erase_244

/-- Pointwise structural transport for `host_semantic.copy_endpoint_values`. -/
theorem erase_245 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    letI : ExternalTypes := base
    ∀ (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1) (tag : aspis_core.field.M31) (lambda : aspis_core.field.QM31) (side : Std.Usize) (values : alloc.vec.Vec (Array (Array aspis_core.field.QM31 2#usize)
  2#usize)) (arity : alloc.vec.Vec (Array Std.Usize 2#usize)),
    @host_semantic.copy_endpoint_values (types base F) (selected base F ops) (PDict_FormatterTypeMaps.trace base F trace) tuple tag lambda side values arity =
    @host_semantic.copy_endpoint_values base ops trace tuple tag lambda side values arity := by
  intro trace tuple tag lambda side values arity
  delta host_semantic.copy_endpoint_values
  try simp only [erase_244 base F ops, PDict_FormatterTypeMaps.trace, PDict_FormatterTypeMaps.compilation]
  all_goals rfl
#print axioms erase_245

/-- Carrier transport candidate for `host_semantic.clone_semantic_columns_loop0.body`. -/
theorem erase_252 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.clone_semantic_columns_loop0.body (types base F) (selected base F ops) = @host_semantic.clone_semantic_columns_loop0.body base ops := by
  delta host_semantic.clone_semantic_columns_loop0.body
  try simp only [erase_117 base F ops]
  all_goals rfl
#print axioms erase_252

/-- Carrier transport candidate for `host_semantic.clone_semantic_columns_loop0`. -/
theorem erase_253 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.clone_semantic_columns_loop0 (types base F) (selected base F ops) = @host_semantic.clone_semantic_columns_loop0 base ops := by
  delta host_semantic.clone_semantic_columns_loop0
  try simp only [erase_252 base F ops]
  all_goals rfl
#print axioms erase_253

/-- Carrier transport candidate for `host_semantic.clone_semantic_columns_loop1.body`. -/
theorem erase_254 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.clone_semantic_columns_loop1.body (types base F) (selected base F ops) = @host_semantic.clone_semantic_columns_loop1.body base ops := by
  delta host_semantic.clone_semantic_columns_loop1.body
  try simp only [erase_117 base F ops]
  all_goals rfl
#print axioms erase_254

/-- Carrier transport candidate for `host_semantic.clone_semantic_columns_loop1`. -/
theorem erase_255 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.clone_semantic_columns_loop1 (types base F) (selected base F ops) = @host_semantic.clone_semantic_columns_loop1 base ops := by
  delta host_semantic.clone_semantic_columns_loop1
  try simp only [erase_254 base F ops]
  all_goals rfl
#print axioms erase_255
end R1Z.PDict_Static222
