import R1Z.PDict_CopyStep222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Pointwise structural transport for `host_semantic.lean_copy_row_values_loop`. -/
theorem erase_247 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    letI : ExternalTypes := base
    ∀ (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) (registry : alloc.vec.Vec
  aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1) (values : alloc.vec.Vec (Array (Array aspis_core.field.QM31 2#usize)
  2#usize)) (arity : alloc.vec.Vec (Array Std.Usize 2#usize)) (count : Std.Usize) (index : Std.Usize),
    @host_semantic.lean_copy_row_values_loop (types base F) (selected base F ops) (PDict_FormatterTypeMaps.trace base F trace) lambda (vecMap (link base F) registry) values arity count index =
    @host_semantic.lean_copy_row_values_loop base ops trace lambda registry values arity count index := by
  intro trace lambda registry values arity count index
  delta host_semantic.lean_copy_row_values_loop
  try simp only [Aeneas.Std.uncurry, erase_246 base F ops]
  all_goals rfl
#print axioms erase_247

end R1Z.PDict_Static222
