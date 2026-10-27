import R1Z.PDict_NoPole222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_PublicLeaves222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem transition (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) (x : @Public b) :
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition
      (types b F) (selected b F ops) (pub b F x) =
    resultMap (late b F) (@aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition b ops x) := by
  change resultMap (late b F) (ops.op225 (unpublic b F (pub b F x))) = _
  rw [public_roundtrip]

theorem bytes (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) (x : @Public b) :
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (types b F) (selected b F ops) (pub b F x) =
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes b ops x := by
  change ops.op226 (unpublic b F (pub b F x)) = _
  rw [public_roundtrip]

theorem helper (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b)
    (x : @Trace b) (n : U64) (l c : aspis_core.field.QM31) :
    @aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1
      (types b F) (selected b F ops) (trace b F x) n l c =
    @aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1 b ops x n l c := by
  change ops.op224 (untrace b F (trace b F x)) n l c = _
  rw [trace_roundtrip]

#print axioms transition
#print axioms bytes
#print axioms helper
end R1Z.PDict_PublicLeaves222
