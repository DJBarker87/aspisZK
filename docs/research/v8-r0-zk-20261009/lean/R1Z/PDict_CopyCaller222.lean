import R1Z.PDict_MapErrTransport222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Pointwise structural transport for `host_semantic.lean_copy_row_values`. -/
theorem erase_248 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) (h12 : PDict_MapErrTransport222.MapErrLaw base ops) :
    letI : ExternalTypes := base
    ∀ (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31),
    @host_semantic.lean_copy_row_values (types base F) (selected base F ops) (PDict_FormatterTypeMaps.trace base F trace) lambda =
    @host_semantic.lean_copy_row_values base ops trace lambda := by
  intro trace lambda
  have hb : @ExternalFuns.op12 base ops = @ProverRwOuterMapErr.map_err := h12
  have ht : @ExternalFuns.op12 (types base F) (selected base F ops) = @ProverRwOuterMapErr.map_err := h12
  have hr : @aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1
      (types base F) (selected base F ops) =
      resultMap (innerMap (vecMap (link base F)))
        (@aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 base ops) := rfl
  delta host_semantic.lean_copy_row_values
  rw [hr]
  simp only [PDict_ResultTransport.bind_map]
  apply PDict_FallibleTransport.bind_congr
  intro r
  simp only [core.result.Result.map_err, ht, hb]
  cases r with
  | Ok v =>
    simp only [innerMap, ProverRwOuterMapErr.map_err]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    have hlen : alloc.vec.Vec.len (vecMap (link base F) v) = alloc.vec.Vec.len v := by
      simp [alloc.vec.Vec.len, vecMap]
    simp only [hlen, erase_247]
    rfl
  | Err e =>
    simp only [innerMap, ProverRwOuterMapErr.map_err]
    rfl
#print axioms erase_248
end R1Z.PDict_Static222
