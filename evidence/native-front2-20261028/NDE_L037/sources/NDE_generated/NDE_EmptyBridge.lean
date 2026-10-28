import NDE_Reference4.Funs
import RPv_FIy_EmptyRootMap
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_EmptyBridge

theorem table : NDE_Reference4.POOL_V1_PAIR_EMPTY_ROOTS_V1 =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 := by
  simp only [NDE_Reference4.POOL_V1_PAIR_EMPTY_ROOTS_V1,
    FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1]

theorem empty_root (level : Usize) : NDE_Reference4.empty_root_ref level =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level := by
  unfold NDE_Reference4.empty_root_ref FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root
  rw [table]
  cases h : Array.index_usize
    FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [h,bind_tc_ok]
    exact (AspisR1.FIy_EmptyRootMap.value a).symm

#print axioms table
#print axioms empty_root
end NDE_EmptyBridge
