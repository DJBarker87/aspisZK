import NDE_ClaimBridge
import NDE_RawBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ClaimResult
open NDE_ClaimBridge

theorem columns :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = ok 28#usize := by
  simp only [FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1,
    FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1,
    FIq_Native.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS]
  rfl

theorem selected_claim (claims : Array Q 84#usize) (point column : Usize) :
    NDE_LiftBridge.mapResult fromRef (NDE_Reference4.claim_ref (claimsToRef claims) point column) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim claims point column := by
  simp only [NDE_Reference4.claim_ref, FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim,
    columns,bind_tc_ok,NDE_RawBridge.map_bind,index_transport]

#print axioms columns
#print axioms selected_claim
end NDE_ClaimResult
