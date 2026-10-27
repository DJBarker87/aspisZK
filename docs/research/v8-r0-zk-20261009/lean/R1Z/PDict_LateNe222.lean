import R1Z.PDict_HelperTransport222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem late_ne (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) (x y : @Late base) :
    core.cmp.impls.PartialEqShared.ne
      (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1 (types base F) (selected base F ops))
      (late base F x) (late base F y) =
    core.cmp.impls.PartialEqShared.ne
      (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1 base ops)
      x y := by
  cases x
  cases y
  rfl

theorem erase_256 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.clone_semantic_columns (types base F) (selected base F ops) =
      @host_semantic.clone_semantic_columns base ops := by
  delta host_semantic.clone_semantic_columns
  simp only [erase_63, erase_253, erase_255]
  all_goals rfl

#print axioms late_ne
#print axioms erase_256
end R1Z.PDict_Static222
